/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Ellipticity

/-!
# CoefficientFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The genuine triadic coefficient family of a cutoff

Every cube receives the same literal coefficient representative
`a_m = nu I + k_m`.  Its local upper ellipticity constant is selected from a
proved compact-cube bound of that continuous representative; compatibility is
therefore pointwise, not an additional assumption or a chosen off-cube
extension.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- Every compact set in this finite-dimensional ambient space lies in an
open origin cube at a nonnegative integer scale. -/
theorem exists_nat_openOriginCube_of_isCompact {K : Set (Vec d)}
    (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ openCubeSet (originCube d (n : ℤ)) := by
  let g : Vec d → ℝ := fun x => 2 * ∑ i : Fin d, |x i|
  have hg : Continuous g := by
    exact continuous_const.mul
      (continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).abs))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ∑ j : Fin d, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hgx : |g x| ≤ C := hC x hx
  have hsum_nn : 0 ≤ ∑ j : Fin d, |x j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg (x j)
  have hsum : 2 * ∑ j : Fin d, |x j| ≤ C := by
    simpa [g, abs_of_nonneg hsum_nn] using hgx
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := by simp
  rw [hpow]
  have hb : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by linarith
  rw [abs_lt] at hb
  exact ⟨by linarith [hb.1], hb.2⟩

/-- The least nonnegative origin-cube scale whose open cube contains the
closure of `Q`.  This canonical depth is geometric data of `Q`, not a chosen
ellipticity witness. -/
noncomputable def cubeOriginCoverDepth (Q : TriadicCube d) : ℕ := by
  classical
  exact Nat.find (exists_nat_openOriginCube_of_isCompact
    ((isBounded_openCubeSet Q).isCompact_closure))

/-- The canonical integer scale associated to `cubeOriginCoverDepth`. -/
noncomputable def cubeOriginCoverScale (Q : TriadicCube d) : ℤ :=
  (cubeOriginCoverDepth Q : ℤ)

theorem closure_subset_originCover (Q : TriadicCube d) :
    closure (openCubeSet Q) ⊆
      openCubeSet (originCube d (cubeOriginCoverScale Q)) := by
  classical
  exact Nat.find_spec (exists_nat_openOriginCube_of_isCompact
    ((isBounded_openCubeSet Q).isCompact_closure))

/-- Minimality makes the enclosing origin scale canonical, rather than an
arbitrary compactness choice. -/
theorem cubeOriginCoverDepth_le (Q : TriadicCube d) (n : ℕ)
    (hn : closure (openCubeSet Q) ⊆ openCubeSet (originCube d (n : ℤ))) :
    cubeOriginCoverDepth Q ≤ n := by
  classical
  exact Nat.find_min' (exists_nat_openOriginCube_of_isCompact
    ((isBounded_openCubeSet Q).isCompact_closure)) hn

theorem openCubeSet_subset_originCover (Q : TriadicCube d) :
    openCubeSet Q ⊆ openCubeSet (originCube d (cubeOriginCoverScale Q)) := by
  exact subset_closure.trans (closure_subset_originCover Q)

/-- The measurable, sample-dependent entry envelope used by the actual
coefficient on `Q`.  It is the molecular constant plus the genuine lower-tail
local control on a deterministic enclosing origin cube. -/
noncomputable def coefficientCutoffCubeEntryBound (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) : ℝ :=
  M.nu + cutoffLocalControl (cubeOriginCoverScale Q) m omega

theorem measurable_coefficientCutoffCubeEntryBound (M : ABKModel d)
    (m : ℤ) (Q : TriadicCube d) :
    Measurable (fun omega : CutoffSample d => coefficientCutoffCubeEntryBound M m omega Q) := by
  exact measurable_const.add (measurable_cutoffLocalControl (cubeOriginCoverScale Q) m)

theorem abs_coefficientCutoff_entry_le_cubeEntryBound (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i j : Fin d) :
    |coefficientCutoff M.nu m omega x i j| ≤
      coefficientCutoffCubeEntryBound M m omega Q := by
  exact abs_coefficientCutoff_entry_le M.nu M.nu_pos.le (cubeOriginCoverScale Q) m omega
    (openCubeSet_subset_originCover Q hx) i j

/-- The actual upper ellipticity constant on one triadic cube.  Its dependence
on the realised cutoff control is retained explicitly; only the lower leg is
the molecular diffusivity. -/
noncomputable def coefficientCutoffCubeEllipticityUpper (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) : ℝ :=
  ((d : ℝ) * (d : ℝ) * (coefficientCutoffCubeEntryBound M m omega Q) ^ 2 + M.nu ^ 2) /
    M.nu

/-- The chosen upper ellipticity constant is measurable in the genuine cutoff
sample.  Its geometric cover is canonical and its random part is precisely
the measurable lower-tail control. -/
theorem measurable_coefficientCutoffCubeEllipticityUpper (M : ABKModel d)
    (m : ℤ) (Q : TriadicCube d) :
    Measurable (fun omega : CutoffSample d =>
      coefficientCutoffCubeEllipticityUpper M m omega Q) := by
  unfold coefficientCutoffCubeEllipticityUpper
  have hbound := measurable_coefficientCutoffCubeEntryBound M m Q
  have hsq : Measurable (fun omega : CutoffSample d =>
      coefficientCutoffCubeEntryBound M m omega Q ^ (2 : ℕ)) :=
    hbound.pow_const 2
  exact ((measurable_const.mul hsq).add measurable_const).div measurable_const

theorem isEllipticFieldOn_coefficientCutoff_cube (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    IsEllipticFieldOn M.nu (coefficientCutoffCubeEllipticityUpper M m omega Q)
      (openCubeSet Q) (coefficientCutoff M.nu m omega) := by
  exact isEllipticFieldOn_coefficientCutoff_of_entry_bound M m omega
    (measurableSet_openCubeSet Q) _
    (fun x hx i j =>
      abs_coefficientCutoff_entry_le_cubeEntryBound M m omega Q hx i j)

/-- The literal Chapter 2 coefficient object of the actual cutoff on one
triadic cube. -/
noncomputable def coefficientCutoffCoeffOn (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) : CoeffOn (cubeDomain Q) where
  toCoeffField := coefficientCutoff M.nu m omega
  lam := M.nu
  Lam := coefficientCutoffCubeEllipticityUpper M m omega Q
  lam_pos := M.nu_pos
  lam_le_Lam :=
    (isEllipticFieldOn_coefficientCutoff_cube M m omega Q).2
      (cubeCenter Q) (by
        rw [← ball_cubeCenter_eq_openCubeSet]
        exact Metric.mem_ball_self (cubeRadius_pos Q)) |>.2.1
  aeStronglyMeasurable := by
    classical
    intro i j
    have hmeas : Measurable (fun x : Vec d =>
        restrictCoeffField (openCubeSet Q) (coefficientCutoff M.nu m omega) x i j) := by
      have hEq : (fun x : Vec d =>
          restrictCoeffField (openCubeSet Q) (coefficientCutoff M.nu m omega) x i j) =
          fun x => if x ∈ openCubeSet Q then coefficientCutoff M.nu m omega x i j else 0 := by
        funext x
        by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
      rw [hEq]
      exact ((coefficientCutoff M.nu m omega).entry_measurable i j).ite
        (measurableSet_openCubeSet Q) measurable_const
    exact hmeas.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact (isEllipticFieldOn_coefficientCutoff_cube M m omega Q).2 x hx

@[simp]
theorem coefficientCutoffCoeffOn_toCoeffField (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    (coefficientCutoffCoeffOn M m omega Q).toCoeffField =
      coefficientCutoff M.nu m omega :=
  rfl

/-- The compatible triadic family associated to the genuine cutoff.  Every
cube uses the same pointwise coefficient field; only its locally derived
ellipticity witness changes with the cube. -/
noncomputable def coefficientCutoffTriadicCoeffFamily (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) : TriadicCoeffFamily d where
  coeffOn := coefficientCutoffCoeffOn M m omega
  restrictsTo_of_subset := by
    intro Q R hRQ
    exact Filter.EventuallyEq.rfl

theorem coefficientCutoffTriadicCoeffFamily_coeffOn_aeeq (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) (Q : TriadicCube d) :
    CoeffOn.AEEq ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q)
      (coefficientCutoffCoeffOn M m omega Q) :=
  Filter.EventuallyEq.rfl

end

end Algsuperdiff.Section3.Cutoff
