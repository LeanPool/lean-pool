/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR3Final
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalMild

/-!
# (R3) of `thm:regularised` at every positive time

Let `u` be a velocity whose nonnegative-time slices represent the global
regularized mild curve (`eq:reg-mild`), and let `p` be the canonical
quadratic pressure of that curve at positive times. If `u` and `p` satisfy
(R1)–(R2) of `thm:regularised`, as the regularized contract of
`prop:leray-limit` states them, then they satisfy the regularized momentum
equation (R3) at every point with positive time. At a point of time `t₀`, the
interval theorem is applied on `[0, t₀ + 1]`. On that interval its canonical
pressure agrees with `p` slice by slice.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

section

/-- The product normed additive group used for spatial and temporal regularity. -/
local instance regularisedR3GlobalNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The product real normed space used for spatial and temporal derivatives. -/
local instance regularisedR3GlobalNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- Joint `C¹` regularity on all positive times restricts to `(0, T]`. -/
private theorem regularisedR3Global_contDiffOn_restrict
    (u : ParabolicPoint → Vec3) (T : ℝ)
    (hC1 : ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) :
    ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)) :=
  fun i => (hC1 i).mono (Set.prod_mono subset_rfl Set.Ioc_subset_Ioi_self)

end

/-- (R3) of `thm:regularised` at every positive time, for a velocity whose
slices represent the global regularized mild curve and the canonical
quadratic pressure of that curve, under (R1)–(R2) stated as in the
regularized contract of `prop:leray-limit`. -/
theorem regularisedR3Global_of_mildCurve
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hCurve : ∀ t : ℝ, 0 ≤ t →
      (fun x : Vec3 => u (x, t)) =ᵐ[volume]
        realVectorL2Representative
          (regularizedGlobalMildCurve ρ ε hε
            (realVectorL2OfCoordinateFunction
              (regUniformMollifiedInitial ρ ε hε a)
              (regMollifiedInitial_isInJ ρ ε hε ha).1)
            (regUniformMollifiedInitial_mildJData ρ ε hε ha) t))
    (hPressure : ∀ z : ParabolicPoint, 0 < z.2 →
      p z = forcedQuadPressure ρ ε hε
        (regularizedGlobalMildCurve ρ ε hε
          (realVectorL2OfCoordinateFunction
            (regUniformMollifiedInitial ρ ε hε a)
            (regMollifiedInitial_isInJ ρ ε hε ha).1)
          (regUniformMollifiedInitial_mildJData ρ ε hε ha)) z)
    (hR12 :
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i j, ContinuousOn (fun z => D z i j)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i j k, ContinuousOn (fun z => DD z i j k)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ i, ContinuousOn (fun z => Dt z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
      (∀ i, ContinuousOn (fun z => Dp z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
         (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
        DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
      (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
            vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
            (∀ i j, |D z i j| ≤ C) ∧
            (∀ i j k, |DD z i j k| ≤ C) ∧
            (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
      (∀ δ T : ℝ, 0 < δ → δ < T →
        (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
        MemLp p 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))))) :
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) := by
  intro D DD Dt Dp
  obtain ⟨⟨hSlice, hL2, _hInit, hDiv⟩, hUc, hDc, hDDc, hDtc, hPc, hDpc, hC1,
    hDdiff, hPdiff, _hBounds, _hLp⟩ := hR12
  set b₀ : RealVectorL2 := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1 with hb₀_def
  set U : ℝ → RealVectorL2 := regularizedGlobalMildCurve ρ ε hε b₀
    (regUniformMollifiedInitial_mildJData ρ ε hε ha) with hU_def
  have hRep : ∀ (t : ℝ) (ht : 0 ≤ t),
      realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t)) (hSlice t ht) = U t :=
    fun t ht => realVectorL2Representative_injective_ae
      ((realVectorL2OfCoordinateFunction_rep _ _).trans (hCurve t ht))
  intro z hz i
  set T : ℝ := z.2 + 1 with hT_def
  have hT : 0 < T := by linarith only [hz]
  let hSliceT : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume := fun t ht => hSlice t ht.1
  have hL2T : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSliceT t.1 t.2)) :=
    hL2.comp (continuous_subtype_val.subtype_mk fun t => t.2.1)
  have hDivT : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)) := fun t ht => hDiv t ht.1
  have hCurveT : ∀ s : ℝ, s ∈ Set.Icc 0 T →
      regularisedIntervalMildCurve u T hT.le hSliceT s = U s := by
    intro s hs
    have hclamp : regularizedMildTimeClamp T hT.le s = (⟨s, hs⟩ : Set.Icc 0 T) :=
      regularizedMildTimeClamp_eq_of_mem T hT.le hs
    simp only [regularisedIntervalMildCurve, hclamp]
    exact hRep s hs.1
  have hMildT : ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSliceT t ht) =
      realHeatOperator t ht.1
        (realVectorL2OfCoordinateFunction
          (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1) -
      regularizedMildStokesIntegral
        (regularizedMildTensorTrajectory ρ ε hε
          (regularisedIntervalMildCurve u T hT.le hSliceT)) t := by
    intro t ht
    rw [hRep t ht.1]
    refine (regularizedGlobalMildCurve_mild ρ ε hε b₀
      (regUniformMollifiedInitial_mildJData ρ ε hε ha) t ht.1).trans ?_
    congr 1
    apply regularizedMildStokesIntegral_congr_Icc
    intro s hs
    simp only [regularizedMildTensorTrajectory]
    rw [hCurveT s ⟨hs.1, hs.2.trans ht.2⟩]
  -- the interval pressure is `p` on every positive slice of the interval
  have hPT : ∀ w : ParabolicPoint, w.2 ∈ Set.Ioc 0 T →
      regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSliceT w = p w := by
    intro w hw
    rw [hPressure w hw.1]
    unfold regularisedIntervalCanonicalPressure forcedQuadPressure
    rw [hCurveT w.2 ⟨hw.1.le, hw.2⟩]
  have hPTslice : ∀ w : ParabolicPoint, w.2 ∈ Set.Ioc 0 T →
      (fun x : Vec3 => regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSliceT
        (x, w.2)) = fun x : Vec3 => p (x, w.2) := by
    intro w hw
    funext x
    exact hPT (x, w.2) hw
  have hPTpartial : ∀ w : ParabolicPoint, w.2 ∈ Set.Ioc 0 T → ∀ k : Fin 3,
      spatialPartial (fun y => regularisedIntervalCanonicalPressure
        ρ ε hε u T hT.le hSliceT y) k w = spatialPartial (fun y => p y) k w := by
    intro w hw k
    unfold spatialPartial
    rw [hPTslice w hw]
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    Set.prod_mono subset_rfl Set.Ioc_subset_Ioi_self
  have hR3 := regularisedR3Final_core ρ ε hε a ha u T hT hSliceT hL2T hDivT hMildT
    (fun i => (hUc i).mono hsub) (fun i j => (hDc i j).mono hsub)
    (fun i j k => (hDDc i j k).mono hsub) (fun i => (hDtc i).mono hsub)
    ((hPc.mono hsub).congr fun w hw => hPT w hw.2)
    (fun k => ((hDpc k).mono hsub).congr fun w hw => hPTpartial w hw.2 k)
    (regularisedR3Global_contDiffOn_restrict u T hC1)
    (fun w hw i j => hDdiff w (hsub hw) i j)
    (fun w hw => by
      rw [hPTslice w hw.2]
      exact hPdiff w (hsub hw))
  have hzT : z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) :=
    ⟨Set.mem_univ _, hz, by linarith only⟩
  have h := hR3.2.1 z hzT i
  rw [hPTpartial z ⟨hz, by linarith only⟩ i] at h
  exact h

end CKN.Leray

end
