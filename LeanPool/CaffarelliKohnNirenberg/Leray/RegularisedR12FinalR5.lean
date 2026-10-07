/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalR1
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEnergyInterval

/-!
# The energy equality (R5) at every nonnegative time

For a velocity whose nonnegative-time slices represent the global regularized
mild curve, whose first spatial partial derivatives are continuous and which
is jointly continuously differentiable at positive times, the interval energy
equality of `thm:regularised` (R5) holds at every nonnegative time.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- The product normed additive group structure for the regularized `R⁵` space-time argument. -/
local instance regR12R5NormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The real normed-space structure for the regularized `R⁵` space-time argument. -/
local instance regR12R5NormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- `thm:regularised` (R5) at every nonnegative time. -/
theorem regR12_R5 (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (u : ParabolicPoint → Vec3)
    (hCurve : ∀ t : ℝ, 0 ≤ t →
      (fun x : Vec3 => u (x, t)) =ᵐ[volume]
        realVectorL2Representative (regR12Curve ρ ε hε a ha t))
    (hDprod : ∀ i j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => u y i) j (z.1, z.2))
      (Set.univ ×ˢ Ioi 0))
    (hC1 : ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
    ∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u (fun z i j => spatialPartial (fun y => u y i) j z) t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^ (2 : ℕ) := by
  intro t ht
  set T : ℝ := t + 1 with hTdef
  have hT : 0 < T := by linarith only [ht]
  let b₀ : RealVectorL2 := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a) (regMollifiedInitial_isInJ ρ ε hε ha).1
  let hb := regUniformMollifiedInitial_mildJData ρ ε hε ha
  have hJ : ∀ s : ℝ, 0 ≤ s →
      RegularizedMildJData (regR12Curve ρ ε hε a ha s) :=
    fun s hs => regularizedGlobalMildCurve_mildJData ρ ε hε b₀ hb s hs
  let hSlice : ∀ s : ℝ, s ∈ Set.Icc 0 T → MemLp (fun x : Vec3 => u (x, s)) 2 volume :=
    fun s hs => (memLp_congr_ae (hCurve s hs.1)).2 (hJ s hs.1).1
  have hRep : ∀ (s : ℝ) (hs : s ∈ Set.Icc 0 T),
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, s)) (hSlice s hs) =
        regR12Curve ρ ε hε a ha s := fun s hs =>
    realVectorL2Representative_injective_ae
      ((realVectorL2OfCoordinateFunction_rep _ _).trans (hCurve s hs.1))
  have hCont : Continuous (fun s : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, s.1)) (hSlice s.1 s.2)) := by
    have hc := (regularizedGlobalMildCurve_continuous ρ ε hε b₀ hb).comp
      (continuous_subtype_val : Continuous (fun s : Set.Icc (0 : ℝ) T => s.1))
    convert hc using 1
    funext s
    exact hRep s.1 s.2
  have hDiv : ∀ s : ℝ, s ∈ Set.Icc 0 T → CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, s)) :=
    fun s hs => regR12_isWeakDivFreeL2_congr (hCurve s hs.1).symm
      (CKN.isInJ_weakDivFree (hJ s hs.1))
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    Set.prod_mono subset_rfl Set.Ioc_subset_Ioi_self
  have hD : ∀ i j, ContinuousOn (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)) :=
    fun i j => (hDprod i j).mono hsub
  have hU : ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)) :=
    fun i => (hC1 i).mono hsub
  have hMild : ∀ s : ℝ, (hs : s ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, s)) (hSlice s hs) =
      realHeatOperator s hs.1 b₀ -
      regularizedMildStokesIntegral
        (regularizedMildTensorTrajectory ρ ε hε
          (fun r => realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, (regularizedMildTimeClamp T hT.le r : Set.Icc 0 T).1))
            (hSlice (regularizedMildTimeClamp T hT.le r : Set.Icc 0 T).1
              (regularizedMildTimeClamp T hT.le r : Set.Icc 0 T).2))) s := by
    intro s hs
    rw [hRep s hs]
    refine (regularizedGlobalMildCurve_mild ρ ε hε b₀ hb s hs.1).trans ?_
    congr 1
    apply regularizedMildStokesIntegral_congr_Icc
    intro r hr
    have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans hs.2⟩
    have hclamp : regularizedMildTimeClamp T hT.le r = (⟨r, hrT⟩ : Set.Icc 0 T) :=
      regularizedMildTimeClamp_eq_of_mem T hT.le hrT
    simp only [regularizedMildTensorTrajectory, hclamp]
    congr 1
    exact (hRep r hrT).symm
  exact regularised_R5_on_interval_of_mild ρ ε hε a ha u T hT hSlice hCont hDiv hD hU hMild t
    ⟨ht, by linarith only⟩

end CKN.Leray
