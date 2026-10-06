/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.PressureLimitLeray
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLocallySquareIntegrableForce
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The pressure limit for the forced regularized problems

The forced regularized pressure is the quadratic Riesz pressure of the
regularized transport tensor plus the fixed force pressure of
`lem:force-pressure`. The force part is the same field for every `ε`, so the
pressure limit of `thm:leray-forced` reduces to the quadratic part: on every
finite slab the quadratic pressures converge in `L^{3/2}` to the Riesz
pressure of `u ⊗ u` (`prop:leray-pressure-limit`), and the limit pressure is
that glued quadratic pressure plus the force pressure.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A quadratic pressure that is almost everywhere measurable on a finite slab
and is the Riesz pressure of `J ⊗ U` on every positive time slice agrees
almost everywhere on the slab with the space-time product pressure. -/
theorem forcedPressureLimit_quadratic_eq_product
    (P : ParabolicPoint → ℝ) (U J : ParabolicPoint → Vec3) (T : ℝ)
    (hPmeas : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => P (parabolicHomeomorph.symm z))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hR4 : ∀ t : ℝ, 0 < t → ∃ hF : ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => J (x, t) i * U (x, t) j)
        (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => P (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (fun x : Vec3 => J (x, t) i * U (x, t) j)))
    (hU : MemLp (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hJ : MemLp (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    (fun z : Vec3 × ℝ => P (parabolicHomeomorph.symm z)) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)]
      lerayProductPressureOnSlab T
        (fun z => J (parabolicHomeomorph.symm z))
        (fun z => U (parabolicHomeomorph.symm z)) hJ hU := by
  classical
  let S : Set (Vec3 × ℝ) := lerayPressureLimitSlab T
  let ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  let jST : Vec3 × ℝ → Vec3 := fun z => J (parabolicHomeomorph.symm z)
  let uST : Vec3 × ℝ → Vec3 := fun z => U (parabolicHomeomorph.symm z)
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    S.indicator (fun z => jST z i * uST z j)
  let hF := rieszPressureSpaceTime_product_memLp_of_slab
    (MeasurableSet.univ.prod measurableSet_Ioo) jST uST
    (fun i => hJ.eval i) (fun j => hU.eval j)
  let q : Vec3 × ℝ → ℝ := rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) F hF
  let pST : Vec3 × ℝ → ℝ := fun z => P (parabolicHomeomorph.symm z)
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict S =
      (volume : Measure Vec3).prod ν := by
    change ((volume : Measure (Vec3 × ℝ)).restrict
      (Set.univ ×ˢ Ioo 0 T)) = _
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
    simp [ν]
  let P' : Vec3 × ℝ → ℝ := hPmeas.mk pST
  have hP'meas : Measurable P' := hPmeas.stronglyMeasurable_mk.measurable
  have hPP' : pST =ᵐ[(volume : Measure Vec3).prod ν] P' := by
    rw [← hprod]
    exact hPmeas.ae_eq_mk
  have hPP'sec : ∀ᵐ t ∂ν, ∀ᵐ x ∂(volume : Measure Vec3),
      pST (x, t) = P' (x, t) := by
    have hsw := (Measure.measurePreserving_swap (μ := ν)
      (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hPP'
    exact Measure.ae_ae_of_ae_prod hsw
  have hqMeas : Measurable q := by
    change Measurable (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF)
    exact rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num) F hF
  have hSlice := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) F hF
  have hSections : ∀ᵐ t ∂ν,
      (fun x : Vec3 => P' (x, t)) =ᵐ[volume] fun x => q (x, t) := by
    filter_upwards [ae_restrict_of_ae hSlice,
      ae_restrict_mem measurableSet_Ioo, hPP'sec] with t hSl ht hPt
    obtain ⟨hFt, hqSlice⟩ := hSl
    obtain ⟨hF2, hP2⟩ := hR4 t ht.1
    have hF32 : ∀ i j : Fin 3,
        MemLp (fun x : Vec3 => J (x, t) i * U (x, t) j)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      intro i j
      have h := hFt i j
      change MemLp (fun x : Vec3 =>
        S.indicator (fun z => jST z i * uST z j) (x, t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume at h
      have hEq : (fun x : Vec3 =>
          S.indicator (fun z => jST z i * uST z j) (x, t)) =
          fun x => J (x, t) i * U (x, t) j := by
        funext x
        simp [S, jST, uST, lerayPressureLimitSlab, ht.1, ht.2]
      exact (memLp_congr_ae (Eventually.of_forall (fun x => congrFun hEq x))).1 h
    have hAgreement := rieszPressureSlice_ae_eq_of_memLp_common
      (2 : ℝ) (by norm_num) (3 / 2 : ℝ) (by norm_num)
      (fun i j x => J (x, t) i * U (x, t) j) hF2 hF32
    have hRep2 := rieszPressureSliceRepresentative_ae_eq
      (2 : ℝ) (by norm_num)
      (fun i j => (hF2 i j).toLp (fun x : Vec3 => J (x, t) i * U (x, t) j))
    have hSliceInput :
        rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t))) =
        rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hF32 i j).toLp
            (fun x : Vec3 => J (x, t) i * U (x, t) j)) := by
      congr 1
      funext i j
      apply Lp.ext
      filter_upwards [(hFt i j).coeFn_toLp, (hF32 i j).coeFn_toLp]
        with x hx₁ hx₂
      rw [hx₁, hx₂]
      simp [F, S, jST, uST, lerayPressureLimitSlab, ht.1, ht.2]
    have hPpoint : (fun x : Vec3 => P (x, t)) =ᵐ[volume]
        fun x => q (x, t) := by
      filter_upwards [hP2, hRep2.symm, hAgreement, hqSlice] with x hp hr ha hq
      calc
        P (x, t) = rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
            (fun i j => (hF2 i j).toLp
              (fun y : Vec3 => J (y, t) i * U (y, t) j)) x := hp
        _ = (rieszPressureSlice (2 : ℝ) (by norm_num)
              (fun i j => (hF2 i j).toLp
                (fun y : Vec3 => J (y, t) i * U (y, t) j)) : Vec3 → ℝ) x := hr
        _ = (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
              (fun i j => (hF32 i j).toLp
                (fun y : Vec3 => J (y, t) i * U (y, t) j)) : Vec3 → ℝ) x := ha
        _ = (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
              (fun i j => (hFt i j).toLp
                (fun y : Vec3 => F i j (y, t))) : Vec3 → ℝ) x := by
          rw [hSliceInput]
        _ = q (x, t) := hq.symm
    filter_upwards [hPpoint, hPt] with x hx hx'
    exact hx'.symm.trans hx
  let E : Set (Vec3 × ℝ) := {z | P' z = q z}
  have hEmeas : MeasurableSet E := measurableSet_eq_fun hP'meas hqMeas
  have hEswap : MeasurableSet {z : ℝ × Vec3 | (z.2, z.1) ∈ E} := by
    change MeasurableSet (Prod.swap ⁻¹' E)
    exact measurableSet_swap_iff.mpr hEmeas
  have hSwap : ∀ᵐ x ∂(volume : Measure Vec3), ∀ᵐ t ∂ν, (x, t) ∈ E :=
    (Measure.ae_ae_comm hEswap).mp hSections
  have hProd : ∀ᵐ z ∂((volume : Measure Vec3).prod ν), z ∈ E :=
    (Measure.ae_prod_iff_ae_ae hEmeas).2 hSwap
  change pST =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict S] q
  rw [hprod]
  filter_upwards [hProd, hPP'] with z hz hz'
  exact hz'.trans hz

/-- The product pressures of one `L³` field on two finite slabs have the same
time slices at every common positive time. -/
private theorem forcedPressureLimit_slab_sections
    (u : Vec3 × ℝ → Vec3) (S R : ℝ)
    (huS : MemLp u 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab S)))
    (huR : MemLp u 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab R))) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → t < S → t < R →
      (fun x : Vec3 => lerayProductPressureOnSlab S u u huS huS (x, t)) =ᵐ[volume]
      (fun x : Vec3 => lerayProductPressureOnSlab R u u huR huR (x, t)) := by
  let FS : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    (lerayPressureLimitSlab S).indicator (fun z => u z i * u z j)
  let FR : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    (lerayPressureLimitSlab R).indicator (fun z => u z i * u z j)
  let hFS := rieszPressureSpaceTime_product_memLp_of_slab
    (MeasurableSet.univ.prod measurableSet_Ioo) u u
    (fun i => huS.eval i) (fun j => huS.eval j)
  let hFR := rieszPressureSpaceTime_product_memLp_of_slab
    (MeasurableSet.univ.prod measurableSet_Ioo) u u
    (fun i => huR.eval i) (fun j => huR.eval j)
  have hSliceS := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) FS hFS
  have hSliceR := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) FR hFR
  filter_upwards [hSliceS, hSliceR] with t hS hR
  intro ht htS htR
  rcases hS with ⟨hFs, hEqS⟩
  rcases hR with ⟨hFr, hEqR⟩
  have hPressure :
      rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFs i j).toLp (fun x : Vec3 => FS i j (x, t))) =
      rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFr i j).toLp (fun x : Vec3 => FR i j (x, t))) := by
    congr 1
    funext i j
    apply Lp.ext
    filter_upwards [(hFs i j).coeFn_toLp, (hFr i j).coeFn_toLp]
      with x h₁ h₂
    rw [h₁, h₂]
    simp [FS, FR, lerayPressureLimitSlab, ht, htS, htR]
  filter_upwards [hEqS, hEqR] with x hxS hxR
  calc
    lerayProductPressureOnSlab S u u huS huS (x, t) =
        (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFs i j).toLp (fun y : Vec3 => FS i j (y, t))) :
            Vec3 → ℝ) x := hxS
    _ = (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFr i j).toLp (fun y : Vec3 => FR i j (y, t))) :
            Vec3 → ℝ) x := by rw [hPressure]
    _ = lerayProductPressureOnSlab R u u huR huR (x, t) := hxR.symm

/-- One measurable field whose restriction to every finite slab is the
product pressure of `u ⊗ u` on that slab: on the slab of height `n + 1` it
is taken from the pressure of that slab, with `n` the least index above the
time coordinate. -/
private theorem forcedPressureLimit_glued_quadratic
    (u : Vec3 × ℝ → Vec3)
    (hu : ∀ T : ℝ, 0 < T → MemLp u 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    ∃ q : Vec3 × ℝ → ℝ, Measurable q ∧ ∀ (T : ℝ) (hT : 0 < T),
      q =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)]
        lerayProductPressureOnSlab T u u (hu T hT) (hu T hT) := by
  classical
  let hUn (n : ℕ) : MemLp u 3
      ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab ((n : ℝ) + 1))) :=
    hu ((n : ℝ) + 1) (by positivity)
  let Q (n : ℕ) : Vec3 × ℝ → ℝ :=
    lerayProductPressureOnSlab ((n : ℝ) + 1) u u (hUn n) (hUn n)
  have hQMeas (n : ℕ) : Measurable (Q n) :=
    rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num) _ _
  have hex : ∀ z : Vec3 × ℝ, ∃ n : ℕ, z.2 < (n : ℝ) + 1 := by
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt z.2
    exact ⟨n, hn.trans (lt_add_one _)⟩
  let q : Vec3 × ℝ → ℝ := fun z => Q (Nat.find (hex z)) z
  have hqMeas : Measurable q :=
    Measurable.find hQMeas
      (fun n => measurableSet_lt measurable_snd measurable_const) hex
  refine ⟨q, hqMeas, ?_⟩
  intro T hT
  let ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  let qT := lerayProductPressureOnSlab T u u (hu T hT) (hu T hT)
  have hqTMeas : Measurable qT :=
    rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num) _ _
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T) =
      (volume : Measure Vec3).prod ν := by
    change ((volume : Measure (Vec3 × ℝ)).restrict
      (Set.univ ×ˢ Ioo 0 T)) = _
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
    simp [ν]
  have hSectionsAll : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ,
      0 < t → t < ((n : ℝ) + 1) → t < T →
        (fun x : Vec3 => Q n (x, t)) =ᵐ[volume]
          (fun x : Vec3 => qT (x, t)) :=
    ae_all_iff.2 fun n => forcedPressureLimit_slab_sections u
      ((n : ℝ) + 1) T (hUn n) (hu T hT)
  let E : Set (Vec3 × ℝ) := {z | q z = qT z}
  have hEmeas : MeasurableSet E := measurableSet_eq_fun hqMeas hqTMeas
  have hSectionsEq : ∀ᵐ t ∂ν, ∀ᵐ x ∂(volume : Measure Vec3), (x, t) ∈ E := by
    filter_upwards [ae_restrict_of_ae hSectionsAll,
      ae_restrict_mem measurableSet_Ioo] with t hAll ht
    have hAll' : ∀ᵐ x ∂(volume : Measure Vec3), ∀ n : ℕ,
        t < ((n : ℝ) + 1) → Q n (x, t) = qT (x, t) := by
      refine ae_all_iff.2 fun n => ?_
      by_cases htn : t < ((n : ℝ) + 1)
      · filter_upwards [hAll n ht.1 htn ht.2] with x hx
        exact fun _ => hx
      · exact Eventually.of_forall fun x h => absurd h htn
    filter_upwards [hAll'] with x hx
    exact hx _ (Nat.find_spec (hex (x, t)))
  have hEswap : MeasurableSet {z : ℝ × Vec3 | (z.2, z.1) ∈ E} := by
    change MeasurableSet (Prod.swap ⁻¹' E)
    exact measurableSet_swap_iff.mpr hEmeas
  have hSwap : ∀ᵐ x ∂(volume : Measure Vec3), ∀ᵐ t ∂ν, (x, t) ∈ E :=
    (Measure.ae_ae_comm hEswap).mp hSectionsEq
  have hProd : ∀ᵐ z ∂((volume : Measure Vec3).prod ν), z ∈ E :=
    (Measure.ae_prod_iff_ae_ae hEmeas).2 hSwap
  rw [hprod]
  exact hProd

/-- The pressure limit of `thm:leray-forced`. The quadratic parts
`p_ε − p_f` of the forced regularized pressures are almost everywhere
measurable on finite slabs and are the Riesz pressures of the regularized
tensors on positive time slices (`lem:regularised-forced`); along every
sequence `ε → 0` a further subsequence of the forced regularized velocities
lies in `L³` on finite slabs (`prop:forced-limit`). Then, whenever the
velocities and their mollifications converge in `L³` on finite slabs to `u`,
the pressures converge in `L^{3/2}` on finite slabs to `p`, where `p − p_f` is
the Riesz pressure of `u ⊗ u` (`prop:leray-pressure-limit`). -/
theorem forcedPressureLimit_of_regularised_pressure_data
    (ρ : RegMollifierProfile)
    (pF : (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ParabolicPoint → ℝ)
    (uε : (a : Vec3 → Vec3) → IsInJ a →
      (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a →
      (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε),
      (∀ T : ℝ, 0 < T →
        MemLp (fun z => pε a ha f hf ε z - pF f hf z) 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
      ∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              regUniformMollifiedVelocity ρ ε hε (uε a ha f hf ε) (x, t) i *
                uε a ha f hf ε (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => pε a ha f hf ε (x, t) - pF f hf (x, t)) =ᵐ[volume]
            rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  regUniformMollifiedVelocity ρ ε hε (uε a ha f hf ε) (x, t) i *
                    uε a ha f hf ε (x, t) j)))
    (hlerayLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ), (∀ n, 0 < εseq n ∧ εseq n ≤ 1) →
      Tendsto εseq atTop (nhds 0) →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto τ atTop atTop ∧
        (∀ T : ℝ, 0 < T → ∀ n : ℕ,
          MemLp (uε a ha f hf (εseq (τ n))) 3
            (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0))
      (σ : ℕ → ℕ) (u : ParabolicPoint → Vec3)
      (hσ : StrictMono σ) (hσtop : Tendsto σ atTop atTop)
      (hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0))
      (hUseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (uε a ha f hf (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0))
      (hJseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1)
            (uε a ha f hf (εseq (σ n))) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0)),
      ∃ p : ParabolicPoint → ℝ,
        ∀ T : ℝ, 0 < T →
          let μ : Measure (Vec3 × ℝ) :=
            (volume : Measure (Vec3 × ℝ)).restrict
              (lerayPressureLimitSlab T)
          let uST : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
          let pST : Vec3 × ℝ → ℝ := fun z => p (parabolicHomeomorph.symm z)
          let pFST : Vec3 × ℝ → ℝ := fun z =>
            pF f hf (parabolicHomeomorph.symm z)
          let pseq : ℕ → Vec3 × ℝ → ℝ := fun n z =>
            pε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm z)
          ∃ hu : MemLp uST 3 μ,
            MemLp (pST - pFST) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
            pST - pFST =ᵐ[μ]
              lerayProductPressureOnSlab T uST uST hu hu ∧
            Tendsto (fun n => eLpNorm (pseq n - pST)
              (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
  intro a ha f hf εseq hseq hεseq σ u hσ hσtop hεsubseq hUseqLthree hJseqLthree
  let εsub : ℕ → ℝ := fun n => εseq (σ n)
  have hseqSub : ∀ n, 0 < εsub n ∧ εsub n ≤ 1 := fun n => hseq (σ n)
  rcases hlerayLimit a ha f hf εsub hseqSub hεsubseq with
    ⟨τ, -, hτtop, hUthree⟩
  let uST : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  have hmpT (T : ℝ) : MeasurePreserving parabolicHomeomorph.symm
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hSmeas : MeasurableSet
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have hpre : parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
          lerayPressureLimitSlab T := by
      ext z
      rfl
    have hmp :=
      parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
    rw [hpre] at hmp
    exact hmp
  have huPar (T : ℝ) (hT : 0 < T) :
      MemLp u 3 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hconv3 : Tendsto
        (fun n => eLpNorm (uε a ha f hf (εsub (τ n)) - u) 3
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, εsub, h3] using
        (hUseqLthree T hT).comp hτtop
    exact Lp.memLp_of_cauchy_tendsto (by norm_num) (hUthree T hT) u hconv3
  have huProduct (T : ℝ) (hT : 0 < T) :
      MemLp uST 3 ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab T)) :=
    (huPar T hT).comp_measurePreserving (hmpT T)
  obtain ⟨qST, -, hqGlue⟩ := forcedPressureLimit_glued_quadratic uST huProduct
  let p : ParabolicPoint → ℝ := fun z => qST (parabolicHomeomorph z) + pF f hf z
  refine ⟨p, ?_⟩
  intro T hT
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)
  let μPar : Measure ParabolicPoint := volume.restrict
    (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let Upar : ℕ → ParabolicPoint → Vec3 :=
    fun n => uε a ha f hf (εseq (σ n))
  let Jpar : ℕ → ParabolicPoint → Vec3 := fun n =>
    regUniformMollifiedVelocity ρ (εseq (σ n)) (hseq (σ n)).1 (Upar n)
  let Uprod : ℕ → Vec3 × ℝ → Vec3 :=
    fun n z => Upar n (parabolicHomeomorph.symm z)
  let Jprod : ℕ → Vec3 × ℝ → Vec3 :=
    fun n z => Jpar n (parabolicHomeomorph.symm z)
  have hmp := hmpT T
  have huParT : MemLp u 3 μPar := huPar T hT
  have huProdT : MemLp uST 3 μ := huProduct T hT
  have hUconvPar : Tendsto (fun n => eLpNorm (Upar n - u)
      (ENNReal.ofReal (3 : ℝ)) μPar) atTop (nhds 0) := hUseqLthree T hT
  have hJconvPar : Tendsto (fun n => eLpNorm (Jpar n - u)
      (ENNReal.ofReal (3 : ℝ)) μPar) atTop (nhds 0) := hJseqLthree T hT
  have hmemOfConv (V : ℕ → ParabolicPoint → Vec3)
      (hV : Tendsto (fun n => eLpNorm (V n - u)
        (ENNReal.ofReal (3 : ℝ)) μPar) atTop (nhds 0)) :
      ∀ᶠ n : ℕ in atTop, MemLp (V n) 3 μPar := by
    have hfinite : ∀ᶠ n : ℕ in atTop,
        eLpNorm (V n - u) (ENNReal.ofReal (3 : ℝ)) μPar < ∞ :=
      hV.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
    filter_upwards [hfinite] with n hn
    have hdiff : MemLp (V n - u) 3 μPar := by
      rw [memLp_iff]
      simpa only [h3] using hn
    have hadd := hdiff.add huParT
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).1 hadd
    simp [Pi.sub_apply]
  have hUmemPar := hmemOfConv Upar hUconvPar
  have hJmemPar := hmemOfConv Jpar hJconvPar
  have hnormEqOf (V : ℕ → ParabolicPoint → Vec3) (n : ℕ)
      (hn : MemLp (V n) 3 μPar) :
      eLpNorm ((fun z => V n (parabolicHomeomorph.symm z)) - uST)
          (ENNReal.ofReal (3 : ℝ)) μ =
        eLpNorm (V n - u) (ENNReal.ofReal (3 : ℝ)) μPar := by
    have h := eLpNorm_comp_measurePreserving
      (p := ENNReal.ofReal (3 : ℝ)) (hn.sub huParT).aestronglyMeasurable hmp
    exact h
  have hUconv : Tendsto (fun n => eLpNorm (Uprod n - uST)
      (ENNReal.ofReal (3 : ℝ)) μ) atTop (nhds 0) := by
    apply hUconvPar.congr'
    filter_upwards [hUmemPar] with n hn
    exact (hnormEqOf Upar n hn).symm
  have hJconv : Tendsto (fun n => eLpNorm (Jprod n - uST)
      (ENNReal.ofReal (3 : ℝ)) μ) atTop (nhds 0) := by
    apply hJconvPar.congr'
    filter_upwards [hJmemPar] with n hn
    exact (hnormEqOf Jpar n hn).symm
  obtain ⟨NU, hNU⟩ := Filter.eventually_atTop.1 hUmemPar
  obtain ⟨NJ, hNJ⟩ := Filter.eventually_atTop.1 hJmemPar
  let N : ℕ := max NU NJ
  let Umod : ℕ → Vec3 × ℝ → Vec3 := fun n => if n < N then uST else Uprod n
  let Jmod : ℕ → Vec3 × ℝ → Vec3 := fun n => if n < N then uST else Jprod n
  have hUmod : ∀ n : ℕ, MemLp (Umod n) 3 μ := by
    intro n
    by_cases hn : n < N
    · simpa [Umod, hn] using huProdT
    · have hnU : NU ≤ n := le_trans (le_max_left NU NJ) (le_of_not_gt hn)
      have h : MemLp (Uprod n) 3 μ := (hNU n hnU).comp_measurePreserving hmp
      simpa [Umod, hn] using h
  have hJmod : ∀ n : ℕ, MemLp (Jmod n) 3 μ := by
    intro n
    by_cases hn : n < N
    · simpa [Jmod, hn] using huProdT
    · have hnJ : NJ ≤ n := le_trans (le_max_right NU NJ) (le_of_not_gt hn)
      have h : MemLp (Jprod n) 3 μ := (hNJ n hnJ).comp_measurePreserving hmp
      simpa [Jmod, hn] using h
  have hUconv3 : Tendsto (fun n => eLpNorm (Umod n - uST) 3 μ)
      atTop (nhds 0) := by
    rw [h3]
    apply hUconv.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [Umod, not_lt_of_ge hn]
  have hJconv3 : Tendsto (fun n => eLpNorm (Jmod n - uST) 3 μ)
      atTop (nhds 0) := by
    rw [h3]
    apply hJconv.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [Jmod, not_lt_of_ge hn]
  have hcanonical := lerayPressureLimit_Lthree T Jmod Umod uST hJmod hUmod
    huProdT hJconv3 hUconv3
  have hqT := hqGlue T hT
  have hdiffEq : (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)) -
      (fun z : Vec3 × ℝ => pF f hf (parabolicHomeomorph.symm z)) = qST := by
    funext z
    simp [p]
  have hquadEq (n : ℕ) (hn : N ≤ n) :
      (fun z : Vec3 × ℝ => pε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm z) -
          pF f hf (parabolicHomeomorph.symm z)) =ᵐ[μ]
        lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) := by
    have hnU : NU ≤ n := le_trans (le_max_left NU NJ) hn
    have hnJ : NJ ≤ n := le_trans (le_max_right NU NJ) hn
    obtain ⟨hR2, hR4⟩ := hregularised a ha f hf (εseq (σ n)) (hseq (σ n)).1
    have hU : MemLp (Uprod n) 3 μ := (hNU n hnU).comp_measurePreserving hmp
    have hJ : MemLp (Jprod n) 3 μ := (hNJ n hnJ).comp_measurePreserving hmp
    have hmeas : AEStronglyMeasurable
        (fun z : Vec3 × ℝ => pε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm z) -
          pF f hf (parabolicHomeomorph.symm z)) μ :=
      ((hR2 T hT).comp_measurePreserving hmp).aestronglyMeasurable
    have hactual := forcedPressureLimit_quadratic_eq_product
      (fun z => pε a ha f hf (εseq (σ n)) z - pF f hf z) (Upar n) (Jpar n) T
      hmeas hR4 hU hJ
    have hJval : Jmod n = Jprod n := by
      simp [Jmod, show ¬ n < N from not_lt_of_ge hn]
    have hUval : Umod n = Uprod n := by
      simp [Umod, show ¬ n < N from not_lt_of_ge hn]
    have hmod : lerayProductPressureOnSlab T (Jprod n) (Uprod n) hJ hU =
        lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) := by
      have key : ∀ (v w : Vec3 × ℝ → Vec3) (hv : MemLp v 3 μ) (hw : MemLp w 3 μ),
          v = Jmod n → w = Umod n →
          lerayProductPressureOnSlab T v w hv hw =
            lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) := by
        intro v w hv hw hvE hwE
        subst hvE hwE
        rfl
      exact key _ _ hJ hU hJval.symm hUval.symm
    filter_upwards [hactual] with z hz
    exact hz.trans (congrFun hmod z)
  have hpressureConv : Tendsto
      (fun n => eLpNorm
        (fun z : Vec3 × ℝ =>
          pε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm z) -
            p (parabolicHomeomorph.symm z))
        (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
    apply hcanonical.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    apply eLpNorm_congr_ae
    filter_upwards [hquadEq n hn, hqT] with z hzP hzq
    have hzp : p (parabolicHomeomorph.symm z) =
        qST z + pF f hf (parabolicHomeomorph.symm z) := by
      simp [p]
    simp only [Pi.sub_apply] at hzP ⊢
    rw [hzp, ← hzP, hzq]
    ring
  have hqMem : MemLp qST (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
    (memLp_congr_ae hqT).2
      ((rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num) _ _).mono_measure
        Measure.restrict_le_self)
  refine ⟨huProdT, ?_, ?_, hpressureConv⟩
  · rw [hdiffEq]
    exact hqMem
  · rw [hdiffEq]
    exact hqT

end CKN.Leray

end
