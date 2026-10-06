/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitSlices
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand

/-!
# The strong form of the equation against a scalar test

A strong solution satisfies its equation, with the specified weak time
derivative and Laplacian, against every scalar space-time test field placed in
one velocity component (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The scalar test placed in the `i`-th velocity component. -/
@[expose] def lpsSingleTest (i : Fin 3) (s : ParabolicPoint → ℝ) : ParabolicPoint → Vec3 :=
  fun z => Pi.single i (s z)

theorem lpsSingleTest_mem {a b : ℝ} (i : Fin 3) {s : ParabolicPoint → ℝ}
    (hs : s ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b)) :
    lpsSingleTest i s ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) := by
  obtain ⟨hd, hc, hsupp⟩ := hs
  have hfun : lpsSingleTest i s = fun z => s z • (Pi.single i (1 : ℝ) : Vec3) := by
    funext z
    rw [← Pi.single_smul' i (s z) (1 : ℝ)]
    simp [lpsSingleTest]
  rw [hfun]
  refine ⟨hd.smul contDiff_const, hc.smul_right, ?_⟩
  exact (tsupport_smul_subset_left _ _).trans hsupp

theorem lpsSingleTest_spatialPartial (i k j : Fin 3) (s : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    CKN.spatialPartial (fun y => lpsSingleTest i s y k) j z =
      if k = i then CKN.spatialPartial s j z else 0 := by
  by_cases hk : k = i
  · subst hk
    simp [lpsSingleTest]
  · have : (fun y => lpsSingleTest i s y k) = fun _ => (0 : ℝ) := by
      funext y
      simp [lpsSingleTest, Pi.single_eq_of_ne hk]
    rw [this]
    simp [hk, CKN.spatialPartial]

theorem lpsSingleTest_timePartial (i k : Fin 3) (s : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    CKN.timePartial (fun y => lpsSingleTest i s y k) z =
      if k = i then CKN.timePartial s z else 0 := by
  by_cases hk : k = i
  · subst hk
    simp [lpsSingleTest]
  · have : (fun y => lpsSingleTest i s y k) = fun _ => (0 : ℝ) := by
      funext y
      simp [lpsSingleTest, Pi.single_eq_of_ne hk]
    rw [this]
    simp [hk, CKN.timePartial]

/-- A space-time test field and its first derivatives are square integrable on
the slab. -/
theorem lps_test_memLp_slab {a b : ℝ} {s : Vec3 × ℝ → ℝ}
    (hs : s ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b)) (j : Fin 3) :
    MemLp s 2 (volume.restrict (vlSlab a b)) ∧
      MemLp (fun z => spatialPartial s j z) 2 (volume.restrict (vlSlab a b)) ∧
      MemLp (fun z => timePartial s z) 2 (volume.restrict (vlSlab a b)) := by
  have h0 : IsFiniteMeasureOnCompacts (volume : Measure (Vec3 × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h1 : MemLp (fun z : Vec3 × ℝ => CKN.spatialPartial s j z) 2
      (volume.restrict (vlSlab a b)) :=
    ((CKN.spatialPartial_contDiff hs.1 j).continuous.memLp_of_hasCompactSupport
      (CKN.hasCompactSupport_spatialPartial hs.2.1 j)).restrict _
  have h2 : MemLp (fun z : Vec3 × ℝ => CKN.timePartial s z) 2
      (volume.restrict (vlSlab a b)) :=
    ((CKN.contDiff_timePartial hs.1).continuous.memLp_of_hasCompactSupport
      (CKN.hasCompactSupport_timePartial hs.2.1)).restrict _
  exact ⟨(hs.1.continuous.memLp_of_hasCompactSupport hs.2.1).restrict _, h1, h2⟩

/-- A strong solution satisfies its equation, in the strong form with its
specified time derivative and Laplacian, against every scalar test placed in
one velocity component (`prop:lps-local-strong`). -/
theorem lps_strong_scalar_equation
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : ∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hD2 : ∀ i j, MemLp (fun z : Vec3 × ℝ => D2u z i j j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hDt : ∀ i, MemLp (fun z : Vec3 × ℝ => Dtu z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hp : MemLp p 2 (volume.restrict (vlSlab t₀ T)))
    (i : Fin 3) {s : ParabolicPoint → ℝ}
    (hs : s ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T)) :
    ∫ z in vlSlab t₀ T,
      (Dtu z i * s z - ∑ j : Fin 3, u z i * u z j * spatialPartial s j z
        - (∑ j : Fin 3, D2u z i j j) * s z - p z * spatialPartial s i z) = 0 := by
  have hEq := hU.2.2.2.2.2 (lpsSingleTest i s) (lpsSingleTest_mem i hs)
  have hpoint : ∀ z : ParabolicPoint,
      (-(∑ k : Fin 3, u z k * timePartial (fun y => lpsSingleTest i s y k) z)
          - ∑ k : Fin 3, ∑ j : Fin 3,
              u z k * u z j * spatialPartial (fun y => lpsSingleTest i s y k) j z
          + ∑ k : Fin 3, ∑ j : Fin 3,
              Du z k j * spatialPartial (fun y => lpsSingleTest i s y k) j z
          - p z * ∑ k : Fin 3, spatialPartial (fun y => lpsSingleTest i s y k) k z) =
        -(u z i * timePartial s z) - ∑ j : Fin 3, u z i * u z j * spatialPartial s j z
          + ∑ j : Fin 3, Du z i j * spatialPartial s j z - p z * spatialPartial s i z := by
    intro z
    have e1 : ∀ f : Fin 3 → Fin 3 → ℝ,
        ∑ x : Fin 3, ∑ x_1 : Fin 3, (if x = i then f x x_1 else 0) = ∑ x_1 : Fin 3, f i x_1 := by
      intro f
      rw [Finset.sum_comm]
      simp
    simp only [lpsSingleTest_spatialPartial, lpsSingleTest_timePartial, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [e1 (fun x x_1 => u z x * u z x_1 * spatialPartial s x_1 z),
      e1 (fun x x_1 => Du z x x_1 * spatialPartial s x_1 z)]
  have hEq' : ∫ z in vlSlab t₀ T,
      (-(u z i * timePartial s z) - ∑ j : Fin 3, u z i * u z j * spatialPartial s j z
        + ∑ j : Fin 3, Du z i j * spatialPartial s j z - p z * spatialPartial s i z) = 0 := by
    have := hEq
    simp only [hpoint] at this
    exact this
  obtain ⟨hsL2, hsx, hst⟩ := lps_test_memLp_slab hs i
  have hsxj : ∀ j, MemLp (fun z => spatialPartial s j z) 2 (volume.restrict (vlSlab t₀ T)) :=
    fun j => (lps_test_memLp_slab hs j).2.1
  obtain ⟨hw1, hw2, hw3⟩ := hDerivs.2.2.2.2 s hs
  have iT : Integrable (fun z : Vec3 × ℝ => u z i * timePartial s z)
      (volume.restrict (vlSlab t₀ T)) := (hu i).integrable_mul hst
  obtain ⟨Cx, hCx⟩ : ∃ C : ℝ, ∀ j : Fin 3, ∀ z : Vec3 × ℝ, ‖spatialPartial s j z‖ ≤ C := by
    have hb := fun j => CKN.exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hs j
    choose C hC using hb
    refine ⟨∑ j, |C j|, fun j z => (hC j z).trans ?_⟩
    exact (le_abs_self (C j)).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg (C j))
        (Finset.mem_univ j))
  have iC : ∀ j, Integrable (fun z : Vec3 × ℝ => u z i * u z j * spatialPartial s j z)
      (volume.restrict (vlSlab t₀ T)) := by
    intro j
    have hprod : Integrable (fun z : Vec3 × ℝ => u z i * u z j)
        (volume.restrict (vlSlab t₀ T)) := (hu i).integrable_mul (hu j)
    have hmul := hprod.mul_bdd (hsxj j).aestronglyMeasurable
      (ae_of_all _ fun z => hCx j z)
    exact hmul.congr (ae_of_all _ fun z => by ring)
  have iD : ∀ j, Integrable (fun z : Vec3 × ℝ => Du z i j * spatialPartial s j z)
      (volume.restrict (vlSlab t₀ T)) := fun j => (hDu i j).integrable_mul (hsxj j)
  have iP : Integrable (fun z : Vec3 × ℝ => p z * spatialPartial s i z)
      (volume.restrict (vlSlab t₀ T)) := hp.integrable_mul (hsxj i)
  have iA : Integrable (fun z : Vec3 × ℝ => Dtu z i * s z)
      (volume.restrict (vlSlab t₀ T)) := (hDt i).integrable_mul hsL2
  have iE : ∀ j, Integrable (fun z : Vec3 × ℝ => D2u z i j j * s z)
      (volume.restrict (vlSlab t₀ T)) := fun j => (hD2 i j).integrable_mul hsL2
  have iCsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ j : Fin 3, u z i * u z j * spatialPartial s j z) (volume.restrict (vlSlab t₀ T)) :=
    integrable_finsetSum _ fun j _ => iC j
  have iDsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ j : Fin 3, Du z i j * spatialPartial s j z) (volume.restrict (vlSlab t₀ T)) :=
    integrable_finsetSum _ fun j _ => iD j
  have iEsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ j : Fin 3, D2u z i j j * s z) (volume.restrict (vlSlab t₀ T)) :=
    integrable_finsetSum _ fun j _ => iE j
  -- the two weak derivative identities, summed
  have hT : ∫ z in vlSlab t₀ T, u z i * timePartial s z =
      -∫ z in vlSlab t₀ T, Dtu z i * s z := hw3 i
  have hS : ∀ j, ∫ z in vlSlab t₀ T, Du z i j * spatialPartial s j z =
      -∫ z in vlSlab t₀ T, D2u z i j j * s z := fun j => hw2 i j j
  have hSsum : ∫ z in vlSlab t₀ T, ∑ j : Fin 3, Du z i j * spatialPartial s j z =
      -∫ z in vlSlab t₀ T, ∑ j : Fin 3, D2u z i j j * s z := by
    rw [integral_finsetSum _ (fun j _ => iD j), integral_finsetSum _ (fun j _ => iE j),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hS j
  have hsplit : ∀ z : Vec3 × ℝ,
      (Dtu z i * s z - ∑ j : Fin 3, u z i * u z j * spatialPartial s j z
        - (∑ j : Fin 3, D2u z i j j) * s z - p z * spatialPartial s i z) =
        (-(u z i * timePartial s z) - ∑ j : Fin 3, u z i * u z j * spatialPartial s j z
          + ∑ j : Fin 3, Du z i j * spatialPartial s j z - p z * spatialPartial s i z)
        + ((Dtu z i * s z + u z i * timePartial s z)
          - ((∑ j : Fin 3, D2u z i j j * s z)
            + ∑ j : Fin 3, Du z i j * spatialPartial s j z)) := by
    intro z
    rw [Finset.sum_mul]
    ring
  have hzero : ∫ z in vlSlab t₀ T,
      ((Dtu z i * s z + u z i * timePartial s z)
        - ((∑ j : Fin 3, D2u z i j j * s z)
          + ∑ j : Fin 3, Du z i j * spatialPartial s j z)) = 0 := by
    have i1 : Integrable (fun z : Vec3 × ℝ => Dtu z i * s z + u z i * timePartial s z)
        (volume.restrict (vlSlab t₀ T)) := iA.add iT
    have i2 : Integrable (fun z : Vec3 × ℝ => (∑ j : Fin 3, D2u z i j j * s z)
        + ∑ j : Fin 3, Du z i j * spatialPartial s j z)
        (volume.restrict (vlSlab t₀ T)) := iEsum.add iDsum
    rw [integral_sub i1 i2, integral_add iA iT, integral_add iEsum iDsum, hT, hSsum]
    ring
  have hEqInt : Integrable (fun z : Vec3 × ℝ =>
      -(u z i * timePartial s z) - ∑ j : Fin 3, u z i * u z j * spatialPartial s j z
        + ∑ j : Fin 3, Du z i j * spatialPartial s j z - p z * spatialPartial s i z)
      (volume.restrict (vlSlab t₀ T)) :=
    (((iT.neg).sub iCsum).add iDsum).sub iP
  have hzeroInt : Integrable (fun z : Vec3 × ℝ =>
      ((Dtu z i * s z + u z i * timePartial s z)
        - ((∑ j : Fin 3, D2u z i j j * s z)
          + ∑ j : Fin 3, Du z i j * spatialPartial s j z)))
      (volume.restrict (vlSlab t₀ T)) := (iA.add iT).sub (iEsum.add iDsum)
  refine (integral_congr_ae (ae_of_all _ hsplit)).trans ?_
  rw [integral_add hEqInt hzeroInt, hEq', hzero]
  ring

end ESS.LPS

end
