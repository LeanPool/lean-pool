/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalR1
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalMollified
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial

/-!
# The time derivative field in (R2)

The classical time derivative of the regularized velocity is the field
`Δu - (J_ε u · ∇) u - ∇p`. From the continuity, strip bounds and slab
integrability of the velocity, its spatial derivatives, the pressure gradient
and the transport velocity, this field is continuous on `ℝ³ × (0,∞)`, bounded
on strips and square integrable on slabs, as required by `thm:regularised`
(R2).
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- The right-hand side `Δu_i - (J_ε u · ∇) u_i - ∂_i p`. -/
@[expose]
def regR12TimeRHS (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (i : Fin 3) : ℝ :=
  (∑ j : Fin 3, spatialPartial (fun y => spatialPartial (fun x => u x i) j y) j z) -
    (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
      spatialPartial (fun y => u y i) j z) -
    spatialPartial (fun y => p y) i z

/-- The time partial derivative is the derivative along the time line. -/
theorem regR12_timePartial_eq_of_hasDerivAt {g : ParabolicPoint → ℝ} {z : ParabolicPoint}
    {c : ℝ} (h : HasDerivAt (fun s : ℝ => g (z.1, s)) c z.2) : timePartial g z = c := by
  unfold timePartial
  rw [h.hasFDerivAt.fderiv]
  simp

/-- The transport velocity is continuous on `ℝ³ × (0,∞)` for the parabolic
topology. -/
theorem regR12_mollifiedVelocity_continuousOn_parabolic (ρ : RegMollifierProfile) (ε : ℝ)
    (hε : 0 < ε) (u : ParabolicPoint → Vec3)
    (hSlice : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i) (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (i : Fin 3) :
    ContinuousOn (fun z => regUniformMollifiedVelocity ρ ε hε u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  have hUprod : ∀ i : Fin 3, ContinuousOn (fun z : Vec3 × ℝ => u z i) (Set.univ ×ˢ Ioi 0) :=
    fun i => regUniform_continuousOn_pullback (hU i) (fun z hz => hz)
  exact regR12_continuousOn_of_prod (S := Set.univ ×ˢ Ioi 0)
    (regR12_mollifiedVelocity_continuousOn ρ ε hε u hSlice hUprod i)

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (u : ParabolicPoint → Vec3)
  (p : ParabolicPoint → ℝ)

/-- The time derivative field is continuous on `ℝ³ × (0,∞)`. -/
theorem regR12TimeRHS_continuousOn
    (hSlice : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i) (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hD : ∀ i j : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDD : ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDp : ∀ i : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (i : Fin 3) :
    ContinuousOn (fun z => regR12TimeRHS ρ ε hε u p z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  unfold regR12TimeRHS
  refine ((continuousOn_finsetSum _ fun j _ => hDD i j j).sub
    (continuousOn_finsetSum _ fun j _ =>
      (regR12_mollifiedVelocity_continuousOn_parabolic ρ ε hε u hSlice hU j).mul
        (hD i j))).sub (hDp i)

/-- A strip bound for the time derivative field. -/
theorem regR12TimeRHS_abs_le
    (hSlice : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (C : ℝ) (t : ℝ) (ht : 0 < t)
    (hUb : ∀ x : Vec3, vec3EuclideanNorm (u (x, t)) ≤ C)
    (hDb : ∀ x : Vec3, ∀ i j : Fin 3, |spatialPartial (fun y => u y i) j (x, t)| ≤ C)
    (hDDb : ∀ x : Vec3, ∀ i j k : Fin 3,
      |spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k (x, t)| ≤ C)
    (hDpb : ∀ x : Vec3, ∀ i : Fin 3, |spatialPartial (fun y => p y) i (x, t)| ≤ C)
    (x : Vec3) (i : Fin 3) :
    |regR12TimeRHS ρ ε hε u p (x, t) i| ≤
      3 * C + 3 * ((C * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)|) * C) + C := by
  have hC : 0 ≤ C := (vec3EuclideanNorm_nonneg _).trans (hUb x)
  have hK : 0 ≤ ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| :=
    integral_nonneg fun _ => abs_nonneg _
  have hJ : ∀ j : Fin 3, |regUniformMollifiedVelocity ρ ε hε u (x, t) j| ≤
      C * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)| :=
    fun j => regR12_mollifiedVelocity_abs_le ρ ε hε u t (hSlice t ht) C
      (fun x' i' => (abs_apply_le_vec3EuclideanNorm _ i').trans (hUb x')) x j
  unfold regR12TimeRHS
  have h1 : |∑ j : Fin 3, spatialPartial (fun y => spatialPartial (fun x => u x i) j y) j (x, t)|
      ≤ 3 * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin 3, |spatialPartial (fun y => spatialPartial (fun x => u x i) j y) j (x, t)|
        ≤ ∑ _j : Fin 3, C := Finset.sum_le_sum fun j _ => hDDb x i j j
      _ = 3 * C := by simp
  have h2 : |∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u (x, t) j *
      spatialPartial (fun y => u y i) j (x, t)| ≤
      3 * ((C * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)|) * C) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin 3, |regUniformMollifiedVelocity ρ ε hε u (x, t) j *
          spatialPartial (fun y => u y i) j (x, t)|
        ≤ ∑ _j : Fin 3, (C * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)|) * C := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hJ j) (hDb x i j) (abs_nonneg _) (by positivity)
      _ = 3 * ((C * ∫ y : Vec3, |regMollifierKernel ρ ε hε (WithLp.toLp 2 y)|) * C) := by simp
  have h3 := hDpb x i
  calc _ ≤ |∑ j : Fin 3, spatialPartial (fun y => spatialPartial (fun x => u x i) j y) j (x, t)|
        + |∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u (x, t) j *
          spatialPartial (fun y => u y i) j (x, t)| +
        |spatialPartial (fun y => p y) i (x, t)| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

/-- Square integrability of the time derivative field on a slab. -/
theorem regR12TimeRHS_memLp_slab (δ T : ℝ)
    (hSlice : ∀ t : ℝ, 0 < t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i) (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hD : ∀ i j : Fin 3, ContinuousOn (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hδ : 0 < δ)
    (hDL2 : ∀ i j : Fin 3, MemLp (fun z : ParabolicPoint => spatialPartial (fun y => u y i) j z)
      2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))))
    (hDDL2 : ∀ i j k : Fin 3, MemLp (fun z : ParabolicPoint =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z)
      2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))))
    (hDpL2 : ∀ i : Fin 3, MemLp (fun z => spatialPartial (fun y => p y) i z)
      2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))))
    (CJ : ℝ) (hJ : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T), ∀ j : Fin 3,
      |regUniformMollifiedVelocity ρ ε hε u z j| ≤ CJ)
    (i : Fin 3) :
    MemLp (fun z => regR12TimeRHS ρ ε hε u p z i) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  have hslab : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    fun z hz => ⟨Set.mem_univ _, lt_trans hδ hz.2.1⟩
  have hprod : ∀ j : Fin 3, MemLp (fun z => regUniformMollifiedVelocity ρ ε hε u z j *
      spatialPartial (fun y => u y i) j z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
    intro j
    have hmeas : AEStronglyMeasurable (fun z => regUniformMollifiedVelocity ρ ε hε u z j *
        spatialPartial (fun y => u y i) j z)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) :=
      (((regR12_mollifiedVelocity_continuousOn_parabolic ρ ε hε u hSlice hU j).mul
        (hD i j)).mono hsub).aestronglyMeasurable hslab
    refine (hDL2 i j).of_le_mul (c := CJ) hmeas ?_
    filter_upwards [ae_restrict_mem hslab] with z hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hJ z hz j) (abs_nonneg _)
  unfold regR12TimeRHS
  exact ((memLp_finsetSum _ fun j _ => hDDL2 i j j).sub
    (memLp_finsetSum _ fun j _ => hprod j)).sub (hDpL2 i)

end CKN.Leray
