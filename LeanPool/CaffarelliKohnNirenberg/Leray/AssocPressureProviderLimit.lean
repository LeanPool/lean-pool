/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureProviderEventual

/-!
# Assoc Pressure Provider Limit

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Product volume on space and the open positive time interval ending at `T`. -/
@[expose]
def associatedPressureProviderMeasure (T : ℝ) : Measure (Vec3 × ℝ) :=
  (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))

private theorem associatedPressureProviderMeasure_eq_restrict (T : ℝ) :
    associatedPressureProviderMeasure T =
      (volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
  calc
    associatedPressureProviderMeasure T =
        ((volume : Measure Vec3).restrict Set.univ).prod
          (volume.restrict (Ioo 0 T)) := by
      simp [associatedPressureProviderMeasure]
    _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
      rw [Measure.prod_restrict]
    _ = (volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
      rw [← Measure.volume_eq_prod Vec3 ℝ]

private theorem associatedPressureProvider_setIntegral_eq_integral
    {T : ℝ} {F : ParabolicPoint → ℝ} :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), F z
      ∂(volume : Measure ParabolicPoint)) =
      ∫ z : Vec3 × ℝ, F (parabolicHomeomorph.symm z)
        ∂associatedPressureProviderMeasure T := by
  rw [setIntegral_parabolic_to_product]
  calc
    (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo 0 T,
        F (parabolicHomeomorph.symm z) ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z : Vec3 × ℝ, F (parabolicHomeomorph.symm z)
        ∂((volume : Measure (Vec3 × ℝ)).restrict
          ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)) := rfl
    _ = ∫ z : Vec3 × ℝ, F (parabolicHomeomorph.symm z)
        ∂associatedPressureProviderMeasure T := by
      rw [← associatedPressureProviderMeasure_eq_restrict]

private theorem associatedPressureProviderTensor_memLp
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (i j : Fin 3) :
    MemLp (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (associatedPressureProviderMeasure T) := by
  let Q : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo 0 T
  have hQ : MeasurableSet Q := MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hbase := associatedPressureTensor_memLp_fiveThirds hLH i j
  have hrestrict := hbase.restrict Q
  rw [← associatedPressureProviderMeasure_eq_restrict] at hrestrict
  have hEq : associatedPressureTensor T u i j =ᵐ[associatedPressureProviderMeasure T]
      (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j) := by
    have hmem : ∀ᵐ z ∂associatedPressureProviderMeasure T, z ∈ Q := by
      rw [associatedPressureProviderMeasure_eq_restrict]
      exact ae_restrict_mem hQ
    filter_upwards [hmem] with z hz
    have hz' : z ∈ parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
      exact hz
    simp [associatedPressureTensor, hz']
  exact (memLp_congr_ae hEq).1 hrestrict

private theorem associatedPressureProviderPressure_memLp
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp
      (rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_fiveThirds hLH))
      (ENNReal.ofReal (5 / 3 : ℝ)) (associatedPressureProviderMeasure T) := by
  have hbase := rieszPressureSpaceTime_memLp (5 / 3 : ℝ) (by norm_num)
    (associatedPressureTensor T u) (associatedPressureTensor_memLp_fiveThirds hLH)
  have hrestrict := hbase.restrict
    ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
  simpa [associatedPressureProviderMeasure] using hrestrict

private theorem associatedPressureProviderProfile_memLp
    {T : ℝ} {K : Set ℝ} (hK : IsCompact K) (r : ℝ)
    (hr : 0 < r) (hmr : 3 < (2 : ℝ) * r) :
    MemLp (associatedPressureSpatialProfile K 2) (ENNReal.ofReal r)
      (associatedPressureProviderMeasure T) := by
  have hbase := associatedPressureSpatialProfile_memLp hK (m := 2) hr hmr
  have hrestrict := hbase.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
  simpa [associatedPressureProviderMeasure] using hrestrict

private theorem associatedPressureMomentumProfileMajorant_integrable
    {T C : ℝ} {K : Set ℝ} {u : Vec3 × ℝ → Vec3}
    {Du : Vec3 × ℝ → Fin 3 → Vec3} {p : Vec3 × ℝ → ℝ}
    (hK : IsCompact K)
    (hU : MemLp u 2 (associatedPressureProviderMeasure T))
    (hDu : MemLp Du 2 (associatedPressureProviderMeasure T))
    (hTensor : ∀ i j, MemLp (fun z => u z i * u z j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (associatedPressureProviderMeasure T))
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      (associatedPressureProviderMeasure T)) :
    Integrable (associatedPressureMomentumProfileMajorant C
      (associatedPressureSpatialProfile K 2) u Du p)
      (associatedPressureProviderMeasure T) := by
  let S : Vec3 × ℝ → ℝ := associatedPressureSpatialProfile K 2
  have hS2 : MemLp S 2 (associatedPressureProviderMeasure T) := by
    simpa [S] using associatedPressureProviderProfile_memLp hK 2 (by norm_num) (by norm_num)
  have hS52 : MemLp S (ENNReal.ofReal (5 / 2 : ℝ))
      (associatedPressureProviderMeasure T) := by
    simpa [S] using associatedPressureProviderProfile_memLp hK (5 / 2) (by norm_num) (by norm_num)
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have : ENNReal.HolderTriple (ENNReal.ofReal (5 / 3 : ℝ))
      (ENNReal.ofReal (5 / 2 : ℝ)) 1 := by
    have h : Real.HolderTriple (5 / 3 : ℝ) (5 / 2 : ℝ) 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hUterm (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => |u z i| * S z) (associatedPressureProviderMeasure T) := by
    have hi : MemLp (fun z : Vec3 × ℝ => u z i) 2
        (associatedPressureProviderMeasure T) := (memLp_pi_iff.mp hU) i
    have hprod : MemLp ((fun z : Vec3 × ℝ => |u z i|) * S) 1
        (associatedPressureProviderMeasure T) := by
      simpa only [Real.norm_eq_abs] using hi.norm.mul hS2
    change Integrable ((fun z : Vec3 × ℝ => |u z i|) * S)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hNterm (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => |u z i * u z j| * S z)
      (associatedPressureProviderMeasure T) := by
    have hprod : MemLp ((fun z : Vec3 × ℝ => |u z i * u z j|) * S) 1
        (associatedPressureProviderMeasure T) := by
      simpa only [Real.norm_eq_abs] using (hTensor i j).norm.mul hS52
    change Integrable ((fun z : Vec3 × ℝ => |u z i * u z j|) * S)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hVterm (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => |Du z i j| * S z)
      (associatedPressureProviderMeasure T) := by
    have hij : MemLp (fun z : Vec3 × ℝ => Du z i j) 2
        (associatedPressureProviderMeasure T) :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    have hprod : MemLp ((fun z : Vec3 × ℝ => |Du z i j|) * S) 1
        (associatedPressureProviderMeasure T) := by
      simpa only [Real.norm_eq_abs] using hij.norm.mul hS2
    change Integrable ((fun z : Vec3 × ℝ => |Du z i j|) * S)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hPterm : Integrable (fun z : Vec3 × ℝ => |p z| * S z)
      (associatedPressureProviderMeasure T) := by
    have hprod : MemLp ((fun z : Vec3 × ℝ => |p z|) * S) 1
        (associatedPressureProviderMeasure T) := by
      simpa only [Real.norm_eq_abs] using hp.norm.mul hS52
    change Integrable ((fun z : Vec3 × ℝ => |p z|) * S)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hUsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, |u z i| * S z) (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    exact hUterm i
  have hNsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3, |u z i * u z j| * S z)
      (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro j hj
    exact hNterm i j
  have hVsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3, |Du z i j| * S z)
      (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro j hj
    exact hVterm i j
  have hPscaled : Integrable (fun z : Vec3 × ℝ => 3 * (|p z| * S z))
      (associatedPressureProviderMeasure T) := hPterm.const_mul 3
  have hsum := (hUsum.add hNsum).add hVsum |>.add hPscaled
  change Integrable (fun z : Vec3 × ℝ => C *
    ((∑ i : Fin 3, |u z i| * S z) +
      (∑ i : Fin 3, ∑ j : Fin 3, |u z i * u z j| * S z) +
      (∑ i : Fin 3, ∑ j : Fin 3, |Du z i j| * S z) +
      3 * (|p z| * S z))) (associatedPressureProviderMeasure T)
  simpa [associatedPressureMomentumProfileMajorant, S, add_assoc] using hsum.const_mul C

private theorem associatedPressureCompactDerivative_memLp
    {T r : ℝ} {f : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    MemLp f (ENNReal.ofReal r) (associatedPressureProviderMeasure T) := by
  have hglobal : MemLp f (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    hf.continuous.memLp_of_hasCompactSupport hfc
  have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
  simpa [associatedPressureProviderMeasure] using hrestrict

private theorem associatedPressureMomentumProductIntegrable_of_test
    {T : ℝ} {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    {p : Vec3 × ℝ → ℝ} {Φ : Vec3 × ℝ → Vec3}
    (hU : MemLp u 2 (associatedPressureProviderMeasure T))
    (hDu : MemLp Du 2 (associatedPressureProviderMeasure T))
    (hTensor : ∀ i j, MemLp (fun z => u z i * u z j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (associatedPressureProviderMeasure T))
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      (associatedPressureProviderMeasure T))
    (hΦ : Φ ∈ CKN.spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo 0 T)) :
    Integrable (associatedPressureMomentumProductIntegrand u Du p Φ)
      (associatedPressureProviderMeasure T) := by
  let dTime (i : Fin 3) : Vec3 × ℝ → ℝ :=
    CKN.timePartialProd (fun z => Φ z i)
  let dSpace (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    CKN.spatialPartialProd (fun z => Φ z i) j
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have : ENNReal.HolderTriple (ENNReal.ofReal (5 / 3 : ℝ))
      (ENNReal.ofReal (5 / 2 : ℝ)) 1 := by
    have h : Real.HolderTriple (5 / 3 : ℝ) (5 / 2 : ℝ) 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hComp (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hΦ i
  have hTimeMem (i : Fin 3) (r : ℝ) : MemLp (dTime i) (ENNReal.ofReal r)
      (associatedPressureProviderMeasure T) := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (dTime i) := CKN.contDiff_timePartial (hComp i).1
    have hcs : HasCompactSupport (dTime i) := CKN.hasCompactSupport_timePartial (hComp i).2.1
    exact associatedPressureCompactDerivative_memLp hsm hcs
  have hSpaceMem (i j : Fin 3) (r : ℝ) : MemLp (dSpace i j) (ENNReal.ofReal r)
      (associatedPressureProviderMeasure T) := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (dSpace i j) :=
      CKN.spatialPartial_contDiff (hComp i).1 j
    have hcs : HasCompactSupport (dSpace i j) :=
      CKN.hasCompactSupport_spatialPartial (hComp i).2.1 j
    exact associatedPressureCompactDerivative_memLp hsm hcs
  have hTimeTerm (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => u z i * dTime i z) (associatedPressureProviderMeasure T) := by
    have hi : MemLp (fun z : Vec3 × ℝ => u z i) 2
        (associatedPressureProviderMeasure T) := (memLp_pi_iff.mp hU) i
    have hTi : MemLp (dTime i) 2 (associatedPressureProviderMeasure T) := by
      simpa using hTimeMem i 2
    have hprod : MemLp ((fun z : Vec3 × ℝ => u z i) * dTime i) 1
        (associatedPressureProviderMeasure T) := hi.mul hTi
    change Integrable ((fun z : Vec3 × ℝ => u z i) * dTime i)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hConvTerm (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => (u z i * u z j) * dSpace i j z)
      (associatedPressureProviderMeasure T) := by
    have hprod : MemLp ((fun z : Vec3 × ℝ => u z i * u z j) * dSpace i j) 1
        (associatedPressureProviderMeasure T) :=
      (hTensor i j).mul (hSpaceMem i j (5 / 2))
    change Integrable ((fun z : Vec3 × ℝ => u z i * u z j) * dSpace i j)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hGradTerm (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => Du z i j * dSpace i j z)
      (associatedPressureProviderMeasure T) := by
    have hij : MemLp (fun z : Vec3 × ℝ => Du z i j) 2
        (associatedPressureProviderMeasure T) :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    have hspaceTwo : MemLp (dSpace i j) 2 (associatedPressureProviderMeasure T) := by
      simpa using hSpaceMem i j 2
    have hprod : MemLp ((fun z : Vec3 × ℝ => Du z i j) * dSpace i j) 1
        (associatedPressureProviderMeasure T) := hij.mul hspaceTwo
    change Integrable ((fun z : Vec3 × ℝ => Du z i j) * dSpace i j)
      (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hPressureTerm (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => p z * dSpace i i z) (associatedPressureProviderMeasure T) := by
    have hprod : MemLp (p * dSpace i i) 1 (associatedPressureProviderMeasure T) :=
      hp.mul (hSpaceMem i i (5 / 2))
    change Integrable (p * dSpace i i) (associatedPressureProviderMeasure T)
    exact memLp_one_iff_integrable.mp hprod
  have hTimeSum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, u z i * dTime i z) (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    exact hTimeTerm i
  have hConvSum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3, (u z i * u z j) * dSpace i j z)
      (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro j hj
    exact hConvTerm i j
  have hGradSum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j z)
      (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro j hj
    exact hGradTerm i j
  have hPressureSum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, p z * dSpace i i z) (associatedPressureProviderMeasure T) := by
    apply integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
    intro i hi
    exact hPressureTerm i
  have hPressure : Integrable (fun z : Vec3 × ℝ =>
      p z * ∑ i : Fin 3, dSpace i i z) (associatedPressureProviderMeasure T) := by
    simpa only [Finset.mul_sum] using hPressureSum
  change Integrable (fun z : Vec3 × ℝ =>
    -(∑ i : Fin 3, u z i * dTime i z)
      - ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * dSpace i j z
      + ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j z
      - p z * ∑ i : Fin 3, dSpace i i z)
    (associatedPressureProviderMeasure T)
  exact (hTimeSum.neg.sub hConvSum).add hGradSum |>.sub hPressure

private theorem associatedPressureEventually_forall_fin_three
    {P : Fin 3 → ℕ → Prop}
    (hP : ∀ i, ∀ᶠ n : ℕ in atTop, P i n) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin 3, P i n := by
  classical
  have hfinite : ∀ s : Finset (Fin 3), ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ s, P i n := by
    intro s
    induction s using Finset.induction_on with
    | empty => filter_upwards [] with n i hi; simp at hi
    | @insert i s hi ih =>
      filter_upwards [hP i, ih] with n hnew hold j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hnew
      · exact hold j hj
  filter_upwards [hfinite Finset.univ] with n hn
  intro i
  exact hn i (Finset.mem_univ i)

private theorem associatedPressureProvider_curl_integral_zero
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) {φP : Vec3 × ℝ → Vec3}
    (hφP : φP ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (p : Vec3 × ℝ → ℝ) (n : ℕ) :
    ∫ z : Vec3 × ℝ, associatedPressureMomentumProductIntegrand
      (fun z => u (parabolicHomeomorph.symm z))
      (fun z => Du (parabolicHomeomorph.symm z)) p
      (associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φP n)) z
      ∂associatedPressureProviderMeasure T = 0 := by
  let μ := associatedPressureProviderMeasure T
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  let V (n : ℕ) : Vec3 × ℝ → Vec3 :=
    associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φP n)
  let Fc : ParabolicPoint → ℝ := fun y =>
    (-(∑ i : Fin 3, u y i * timePartial
        (fun w => V n (parabolicHomeomorph w) i) y))
      - ∑ i : Fin 3, ∑ j : Fin 3,
          u y i * u y j * spatialPartial
            (fun w => V n (parabolicHomeomorph w) i) j y
      + ∑ i : Fin 3, ∑ j : Fin 3,
          Du y i j * spatialPartial
            (fun w => V n (parabolicHomeomorph w) i) j y
  have hcurl := associatedPressureHelmholtzCutoffCurl_momentum_zero hLH hφP n
  have hcurl' :
      (∫ y in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), Fc y
        ∂(volume : Measure ParabolicPoint)) = 0 := by
    simpa [Fc] using hcurl
  rw [associatedPressureProvider_setIntegral_eq_integral (F := Fc)] at hcurl'
  have hpoint (z : Vec3 × ℝ) :
      Fc (parabolicHomeomorph.symm z) =
        associatedPressureMomentumProductIntegrand uP DuP p (V n) z := by
    have hVcomp (i : Fin 3) :
        (fun w : ParabolicPoint => V n (parabolicHomeomorph w) i) =
          (show ParabolicPoint → ℝ from fun q : Vec3 × ℝ => V n q i) := by
      funext w
      simpa only [parabolicHomeomorph_apply] using
        congrArg (fun v : Vec3 => v i)
          (congrArg (V n) (Prod.mk.eta (p := w)))
    have htime (i : Fin 3) :
        timePartial (fun w : ParabolicPoint =>
          V n (parabolicHomeomorph w) i) (parabolicHomeomorph.symm z) =
        CKN.timePartialProd (fun q : Vec3 × ℝ => V n q i) z := by
      change timePartial (fun w : ParabolicPoint =>
        V n (parabolicHomeomorph w) i) (parabolicHomeomorph.symm z) =
        timePartial (show ParabolicPoint → ℝ from
          fun q : Vec3 × ℝ => V n q i) z
      rw [hVcomp i]
      rfl
    have hspace (i j : Fin 3) :
        spatialPartial (fun w : ParabolicPoint =>
          V n (parabolicHomeomorph w) i) j (parabolicHomeomorph.symm z) =
        CKN.spatialPartialProd (fun q : Vec3 × ℝ => V n q i) j z := by
      change spatialPartial (fun w : ParabolicPoint =>
        V n (parabolicHomeomorph w) i) j (parabolicHomeomorph.symm z) =
        spatialPartial (show ParabolicPoint → ℝ from
          fun q : Vec3 × ℝ => V n q i) j z
      rw [hVcomp i]
      rfl
    calc
      Fc (parabolicHomeomorph.symm z) =
          (-(∑ i : Fin 3, uP z i * CKN.timePartialProd
              (fun q => V n q i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                uP z i * uP z j * CKN.spatialPartialProd (fun q => V n q i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                DuP z i j * CKN.spatialPartialProd (fun q => V n q i) j z := by
            simp only [Fc, htime, hspace, uP, DuP]
      _ = associatedPressureMomentumProductIntegrand uP DuP p (V n) z :=
        (associatedPressureMomentumProductIntegrand_pressureless_curl
          ((associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction
            hφP n).1) z).symm
  calc
    _ = ∫ z : Vec3 × ℝ, Fc (parabolicHomeomorph.symm z) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact (hpoint z).symm
    _ = 0 := hcurl'


private theorem associatedPressureProvider_gradient_integral_zero
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) {φP : Vec3 × ℝ → Vec3}
    (hφP : φP ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) (n : ℕ) :
    ∫ z : Vec3 × ℝ, associatedPressureMomentumProductIntegrand
      (fun z => u (parabolicHomeomorph.symm z))
      (fun z => Du (parabolicHomeomorph.symm z))
      (rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_fiveThirds hLH))
      (associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotentialCutoff φP n)) z
      ∂associatedPressureProviderMeasure T = 0 := by
  let μ := associatedPressureProviderMeasure T
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  let F := associatedPressureTensor T u
  let hF := associatedPressureTensor_memLp_fiveThirds hLH
  let p : Vec3 × ℝ → ℝ := rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF
  let G (n : ℕ) : Vec3 × ℝ → Vec3 :=
    associatedPressureTestGradient (associatedPressureHelmholtzScalarPotentialCutoff φP n)
  have hgrad := associatedPressureHelmholtzScalarPotentialCutoffGradient_momentum_zero
    hLH hφP n
  have hψsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzScalarPotentialCutoff φP n) :=
    (associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction
      hφP n).1
  have htrace (z : Vec3 × ℝ) :
      (∑ i : Fin 3, CKN.spatialSecondPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φP n) i i z) =
      rieszPressureJointLaplacian
        (associatedPressureHelmholtzScalarPotentialCutoff φP n) z := by
    rw [rieszPressureJointLaplacian]
    apply Finset.sum_congr rfl
    intro i hi
    change CKN.mixedSecond
        (fun x : Vec3 => associatedPressureHelmholtzScalarPotentialCutoff φP n
          (x, z.2)) i i z.1 = _
    exact rieszPressure_sliceMixedSecond_eq_joint hψsmooth i i z
  have htrace' (z : Vec3 × ℝ) :
      (∑ i : Fin 3, CKN.spatialPartialProd
        (fun q => CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φP n) i q) i z) =
      rieszPressureJointLaplacian
        (associatedPressureHelmholtzScalarPotentialCutoff φP n) z := by
    calc
      _ = ∑ i : Fin 3, CKN.spatialSecondPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φP n) i i z := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = _ := htrace z
  have htimeDerivative (i : Fin 3) (z : Vec3 × ℝ) :
      CKN.timePartialProd
        (fun q => CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φP n) i q) z =
      CKN.timePartialProd
        (CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φP n) i) z := by
    rfl
  have hspaceDerivative (i j : Fin 3) (z : Vec3 × ℝ) :
      CKN.spatialPartialProd
        (fun q => CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φP n) i q) j z =
      CKN.spatialSecondPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φP n) i j z := by
    rfl
  have hEq (z : Vec3 × ℝ) :
      associatedPressureMomentumProductIntegrand uP DuP p (G n) z =
        (-(∑ i : Fin 3, uP z i * CKN.timePartialProd
            (CKN.spatialPartialProd
              (associatedPressureHelmholtzScalarPotentialCutoff φP n) i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              uP z i * uP z j * CKN.spatialSecondPartialProd
                (associatedPressureHelmholtzScalarPotentialCutoff φP n) i j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DuP z i j * CKN.spatialSecondPartialProd
                (associatedPressureHelmholtzScalarPotentialCutoff φP n) i j z
          - p z * rieszPressureJointLaplacian
              (associatedPressureHelmholtzScalarPotentialCutoff φP n) z := by
    change associatedPressureMomentumProductIntegrand uP DuP p
        (associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotentialCutoff φP n)) z = _
    simp only [associatedPressureMomentumProductIntegrand,
      associatedPressureTestGradient]
    rw [htrace']
    simp only [htimeDerivative, hspaceDerivative]
  calc
    _ = ∫ z : Vec3 × ℝ,
        (-(∑ i : Fin 3, uP z i * CKN.timePartialProd
            (CKN.spatialPartialProd
              (associatedPressureHelmholtzScalarPotentialCutoff φP n) i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              uP z i * uP z j * CKN.spatialSecondPartialProd
                (associatedPressureHelmholtzScalarPotentialCutoff φP n) i j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DuP z i j * CKN.spatialSecondPartialProd
                (associatedPressureHelmholtzScalarPotentialCutoff φP n) i j z
          - p z * rieszPressureJointLaplacian
              (associatedPressureHelmholtzScalarPotentialCutoff φP n) z ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact hEq z
    _ = 0 := by
      simpa [uP, DuP, p, F, hF, μ, associatedPressureProviderMeasure] using hgrad


private theorem associatedPressureProvider_add_integral_zero
    {μ : Measure (Vec3 × ℝ)} {u : Vec3 × ℝ → Vec3}
    {Du : Vec3 × ℝ → Fin 3 → Vec3} {p : Vec3 × ℝ → ℝ}
    {V G : Vec3 × ℝ → Vec3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hVint : Integrable (fun z => associatedPressureMomentumProductIntegrand u Du p V z) μ)
    (hGint : Integrable (fun z => associatedPressureMomentumProductIntegrand u Du p G z) μ)
    (hVzero : ∫ z, associatedPressureMomentumProductIntegrand u Du p V z ∂μ = 0)
    (hGzero : ∫ z, associatedPressureMomentumProductIntegrand u Du p G z ∂μ = 0) :
    ∫ z, associatedPressureMomentumProductIntegrand u Du p (fun q => V q + G q) z ∂μ = 0 := by
  have heq : (fun z => associatedPressureMomentumProductIntegrand u Du p
      (fun q => V q + G q) z) =
      (fun z => associatedPressureMomentumProductIntegrand u Du p V z +
        associatedPressureMomentumProductIntegrand u Du p G z) :=
    funext fun z => associatedPressureMomentumProductIntegrand_add hV hG z
  rw [heq, integral_add hVint hGint, hVzero, hGzero, add_zero]

/-- The selected Riesz pressure gives the unrestricted-test momentum identity
for every finite-time Leray--Hopf solution, as in `thm:assoc-pressure`. -/
theorem associatedPressureForSolution_momentum_identity
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ CKN.spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z
          - associatedPressureForSolution hLH z *
            ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0 := by
  let μ := associatedPressureProviderMeasure T
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  let F := associatedPressureTensor T u
  let hF := associatedPressureTensor_memLp_fiveThirds hLH
  let p : Vec3 × ℝ → ℝ := rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF
  have hU : MemLp uP 2 μ := by
    simpa [uP, μ, associatedPressureProviderMeasure] using
      associatedPressureSolution_velocity_memLp_two_productSlab hLH
  have hDu : MemLp DuP 2 μ := by
    simpa [DuP, μ, associatedPressureProviderMeasure] using
      associatedPressureSolution_gradient_memLp_two_productSlab hLH
  have hTensor (i j : Fin 3) : MemLp (fun z : Vec3 × ℝ => uP z i * uP z j)
      (ENNReal.ofReal (5 / 3 : ℝ)) μ := by
    simpa [uP, μ] using associatedPressureProviderTensor_memLp hLH i j
  have hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ)) μ := by
    simpa [p, μ] using associatedPressureProviderPressure_memLp hLH
  intro φ hφ
  let φP : Vec3 × ℝ → Vec3 := fun z => φ ((z.1, z.2) : ParabolicPoint)
  have hφEq : φP = (show Vec3 × ℝ → Vec3 from φ) := by
    funext z
    simp [φP]
  have hφP : φP ∈ CKN.spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioo 0 T) := by
    have hφ' : (show Vec3 × ℝ → Vec3 from φ) ∈
        CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) := hφ
    rw [hφEq]
    exact hφ'
  let V (n : ℕ) : Vec3 × ℝ → Vec3 :=
    associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φP n)
  let G (n : ℕ) : Vec3 × ℝ → Vec3 :=
    associatedPressureTestGradient (associatedPressureHelmholtzScalarPotentialCutoff φP n)
  let Φ (n : ℕ) : Vec3 × ℝ → Vec3 := associatedPressureHelmholtzTestCutoff φP n
  obtain ⟨K, hK, hKsub, C, hC, hderiv⟩ :=
    associatedPressureHelmholtzTestCutoff_derivative_profile_bounds hφP
  let S : Vec3 × ℝ → ℝ := associatedPressureSpatialProfile K 2
  have hSnonneg (z : Vec3 × ℝ) : 0 ≤ S z := by
    by_cases hz : z.2 ∈ K
    · simp only [S, associatedPressureSpatialProfile, Set.indicator_of_mem hz, one_mul]
      positivity
    · simp only [S, associatedPressureSpatialProfile, Set.indicator_of_notMem hz, zero_mul,
        le_refl]
  let M : Vec3 × ℝ → ℝ :=
    associatedPressureMomentumProfileMajorant C S uP DuP p
  have hMint : Integrable M μ := by
    simpa [M, S, μ] using
      associatedPressureMomentumProfileMajorant_integrable hK hU hDu hTensor hp
  have hTestV (n : ℕ) :=
    associatedPressureHelmholtzCutoffCurl_mem_spaceTimeTestFunction hφP n
  have hTestG (n : ℕ) :=
    associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction hφP n
  have hTestΦ (n : ℕ) := associatedPressureHelmholtzTestCutoff_mem_spaceTimeTestFunction hφP n
  have hVInt (n : ℕ) : Integrable
      (associatedPressureMomentumProductIntegrand uP DuP p (V n)) μ := by
    simpa [μ] using associatedPressureMomentumProductIntegrable_of_test
      hU hDu hTensor hp (hTestV n)
  have hGInt (n : ℕ) : Integrable
      (associatedPressureMomentumProductIntegrand uP DuP p (G n)) μ := by
    simpa [μ] using associatedPressureMomentumProductIntegrable_of_test
      hU hDu hTensor hp (hTestG n)
  have hΦInt (n : ℕ) : Integrable
      (associatedPressureMomentumProductIntegrand uP DuP p (Φ n)) μ := by
    simpa [μ, Φ] using associatedPressureMomentumProductIntegrable_of_test
      hU hDu hTensor hp (hTestΦ n)
  have hTimeBound (n : ℕ) : ∀ z i,
      |CKN.timePartialProd (fun q => Φ n q i) z| ≤ C * S z := by
    intro z i
    exact (hderiv n z i 0).1
  have hSpaceBound (n : ℕ) : ∀ z i j,
      |CKN.spatialPartialProd (fun q => Φ n q i) j z| ≤ C * S z := by
    intro z i j
    exact (hderiv n z i j).2
  have hΦbound (n : ℕ) (z : Vec3 × ℝ) :
      |associatedPressureMomentumProductIntegrand uP DuP p (Φ n) z| ≤ M z := by
    simpa [M, S] using
      associatedPressureMomentumProductIntegrand_abs_le_profileMajorant
        (hTimeBound n) (hSpaceBound n) z
  let I (n : ℕ) (z : Vec3 × ℝ) :=
    associatedPressureMomentumProductIntegrand uP DuP p (Φ n) z
  let I₀ : Vec3 × ℝ → ℝ :=
    associatedPressureMomentumProductIntegrand uP DuP p φP
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (I n) μ := by
    intro n
    exact (hΦInt n).aestronglyMeasurable
  have hdom : ∀ n : ℕ, ∀ᵐ z ∂μ, ‖I n z‖ ≤ M z := by
    intro n
    filter_upwards [] with z
    simpa [I, Real.norm_eq_abs] using hΦbound n z
  have htimeEv (i : Fin 3) (z : Vec3 × ℝ) : ∀ᶠ n : ℕ in atTop,
      CKN.timePartialProd (fun q => Φ n q i) z =
        CKN.timePartialProd (fun q => φP q i) z :=
    associatedPressureHelmholtzTestCutoff_time_eventually_eq hφP i z
  have hspaceEv (i j : Fin 3) (z : Vec3 × ℝ) : ∀ᶠ n : ℕ in atTop,
      CKN.spatialPartialProd (fun q => Φ n q i) j z =
        CKN.spatialPartialProd (fun q => φP q i) j z :=
    associatedPressureHelmholtzTestCutoff_spatial_eventually_eq hφP i j z
  have htimeAll (z : Vec3 × ℝ) : ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin 3,
        CKN.timePartialProd (fun q => Φ n q i) z =
          CKN.timePartialProd (fun q => φP q i) z :=
    associatedPressureEventually_forall_fin_three (fun i => htimeEv i z)
  have hspaceAll (z : Vec3 × ℝ) : ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin 3,
        CKN.spatialPartialProd (fun q => Φ n q i) j z =
          CKN.spatialPartialProd (fun q => φP q i) j z := by
    apply associatedPressureEventually_forall_fin_three
    intro i
    exact associatedPressureEventually_forall_fin_three (fun j => hspaceEv i j z)
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n => I n z) atTop (𝓝 (I₀ z)) := by
    filter_upwards [] with z
    have heq : ∀ᶠ n : ℕ in atTop, I n z = I₀ z := by
      filter_upwards [htimeAll z, hspaceAll z] with n ht hs
      simp [I, I₀, associatedPressureMomentumProductIntegrand, ht, hs]
    exact (tendsto_const_nhds (x := I₀ z)).congr' (.symm heq)
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (bound := M) (F := I) (f := I₀)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hdom) hMint hlim
  have hCutoffZero (n : ℕ) : ∫ z : Vec3 × ℝ, I n z ∂μ = 0 := by
    exact associatedPressureProvider_add_integral_zero
      (hTestV n).1 (hTestG n).1 (hVInt n) (hGInt n)
      (associatedPressureProvider_curl_integral_zero hLH hφP p n)
      (associatedPressureProvider_gradient_integral_zero hLH hφP n)
  have hIntegralLimit : ∫ z : Vec3 × ℝ, I₀ z ∂μ = 0 := by
    have hconstant : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have hZeroSequence : ∀ n : ℕ, ∫ z : Vec3 × ℝ, I n z ∂μ = 0 := hCutoffZero
    have hlim0 : Tendsto (fun n : ℕ => ∫ z : Vec3 × ℝ, I n z ∂μ) atTop (𝓝 0) := by
      exact hconstant.congr' (Filter.Eventually.of_forall fun n => (hZeroSequence n).symm)
    exact tendsto_nhds_unique hDCT hlim0
  have hOriginalIntegrand (z : ParabolicPoint) :
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          Du z i j * spatialPartial (fun y => φ y i) j z
        - associatedPressureForSolution hLH z *
          ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) =
      I₀ (z.1, z.2) := by
      change
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z
          - associatedPressureForSolution hLH z *
            ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) =
          I₀ (parabolicHomeomorph z)
      have hbridge : parabolicHomeomorph z = z := by
        simpa only [parabolicHomeomorph_apply] using (Prod.mk.eta (p := z))
      have hpressure : associatedPressureForSolution hLH z =
          p (parabolicHomeomorph z) := by
        rfl
      change
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z
          - associatedPressureForSolution hLH z *
            ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) =
        associatedPressureMomentumProductIntegrand uP DuP p φP
          (parabolicHomeomorph z)
      rw [hpressure, hbridge]
      simp [φP, associatedPressureMomentumProductIntegrand, uP, DuP, p, F,
        CKN.timePartialProd, CKN.spatialPartialProd, Prod.mk.eta]
      rfl
  let Forig : ParabolicPoint → ℝ := fun z =>
    (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
      - ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * spatialPartial (fun y => φ y i) j z
      + ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * spatialPartial (fun y => φ y i) j z
      - associatedPressureForSolution hLH z *
        ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
  calc
    _ = ∫ z : Vec3 × ℝ, Forig (parabolicHomeomorph.symm z) ∂μ :=
      associatedPressureProvider_setIntegral_eq_integral (F := Forig)
    _ = ∫ z : Vec3 × ℝ, I₀ z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa [Forig, parabolicHomeomorph_apply, parabolicHomeomorph_symm_apply] using
        hOriginalIntegrand (parabolicHomeomorph.symm z)
    _ = 0 := hIntegralLimit

end CKN.Leray

end
