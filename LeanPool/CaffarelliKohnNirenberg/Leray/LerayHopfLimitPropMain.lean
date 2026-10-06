/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropLH1
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropLH2
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropPairingModulus
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropMollifier
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergyIneq
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureLp
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# The limit of the regularized solutions is a Leray–Hopf solution

This is `prop:leray-hopf-limit`: for the subsequence and limit fields of
`prop:leray-limit`, and every `T > 0`, the limit satisfies the clauses
(LH1)–(LH5) of `def:leray-hopf` on `ℝ³ × [0,T]`. The inputs are the
regularized solutions of `thm:regularised` with their energy equality, the
regularized momentum identity of `lem:reg-momentum`, and the convergence
statements of `prop:leray-limit`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- `prop:leray-hopf-limit`: the limit fields of `prop:leray-limit` are, on
every finite slab, a Leray–Hopf solution with the given initial datum. -/
theorem lerayHopfLimit
    (ρ : CKN.Leray.RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := uε a ha ε
      let p := pε a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i =>
        timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i =>
        spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          CKN.Leray.realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
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
            (∀ i, |Dt z i| ≤ C) ∧
            (∀ i, |Dp z i| ≤ C)) ∧
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
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
        Dt z i - (∑ j : Fin 3, DD z i j j) +
          (∑ j : Fin 3,
            CKN.Leray.regUniformMollifiedVelocity ρ ε hε u z j * D z i j) +
          Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * CKN.Leray.regUniformDissipation u D t =
            eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ)))
    (hregMomentum : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε) (φ : ParabolicPoint → Vec3),
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, uε a ha ε z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                (uε a ha ε) z j * uε a ha ε z i *
                spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              spatialPartial (fun y => uε a ha ε y i) j z *
                spatialPartial (fun y => φ y i) j z
          - pε a ha ε z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0)
    (hlerayLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (_hεseq : Tendsto εseq atTop (nhds 0)),
      ∃ σ : ℕ → ℕ, ∃ u : ParabolicPoint → Vec3,
        ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        StrictMono σ ∧ Tendsto σ atTop atTop ∧
        Tendsto (fun n => εseq (σ n)) atTop (nhds 0) ∧
        (∀ x : Vec3, u (x, 0) = a x) ∧
        (∀ T : ℝ, 0 < T →
          let μ : Measure ParabolicPoint :=
            volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
          let U : ℕ → ParabolicPoint → Vec3 :=
            fun n => uε a ha (εseq (σ n))
          let J : ℕ → ParabolicPoint → Vec3 := fun n =>
            CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
              (by exact (hseq (σ n)).1) (U n)
          let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
            spatialPartial (fun y => U n y i) j z
          AEStronglyMeasurable u μ ∧ AEStronglyMeasurable Du μ ∧
          MemLp u 2 μ ∧ MemLp Du 2 μ ∧
          Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
          (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
            Tendsto (fun n => ∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
              atTop (nhds (∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) ∧
          (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
            Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
              atTop (nhds 0)) ∧
          (∀ n, MemLp (U n) 3 μ) ∧
          (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
          Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) ∧
          (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
            MemLp w 2 volume →
            Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
                U n (x, t) i * w x i) atTop
              (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
          (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
            HasWeakGradientOn (Set.univ : Set Vec3)
              (fun x => u (x, t) i) (fun x => Du (x, t) i))) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y =>
                uε a ha (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z)) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0)),
      let hlim := hlerayLimit a ha εseq hseq hεseq
      let _σ := Classical.choose hlim
      let hlim₁ := Classical.choose_spec hlim
      let u := Classical.choose hlim₁
      let hlim₂ := Classical.choose_spec hlim₁
      let Du := Classical.choose hlim₂
      ∀ T : ℝ, 0 < T → IsLerayHopfSolution T a u Du := by
  intro a ha εseq hseq hεseq hlim σ hlim₁ u hlim₂ Du T hT
  obtain ⟨hσmono, hσtop, hεsub, hu0, hslabAll, hrep⟩ := Classical.choose_spec hlim₂
  obtain ⟨huAE, hDuAE, huL2, hDuL2, _, hDweak, hUconvq, hUL3, hJL3, huL3, hJconv,
    hweakSlice, hgrad⟩ := hslabAll T hT
  have hu0' : ∀ x, u (x, 0) = a x := hu0
  -- the regularized solutions along the subsequence
  have hεn : ∀ n, 0 < εseq (σ n) := fun n => (hseq (σ n)).1
  let U : ℕ → ParabolicPoint → Vec3 := fun n => uε a ha (εseq (σ n))
  let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
    spatialPartial (fun y => U n y i) j z
  have hR := fun n => hregularised a ha (εseq (σ n)) (hεn n)
  have c0 := fun n => (hR n).1
  have hSliceMem : ∀ n t, 0 ≤ t → MemLp (fun x => U n (x, t)) 2 volume :=
    fun n => (c0 n).1
  have hSliceCont := fun n => (c0 n).2.1
  have hSlice0 := fun n => (c0 n).2.2.1
  have hSliceDiv : ∀ n t, 0 ≤ t → IsWeakDivFreeL2 (fun x => U n (x, t)) :=
    fun n => (c0 n).2.2.2
  have c1 := fun n => (hR n).2.1
  have c2 := fun n => (hR n).2.2.1
  have c3 := fun n => (hR n).2.2.2.1
  have c4 := fun n => (hR n).2.2.2.2.1
  have c5 := fun n => (hR n).2.2.2.2.2.1
  have c6 := fun n => (hR n).2.2.2.2.2.2.1
  have c7 := fun n => (hR n).2.2.2.2.2.2.2.1
  have c8 := fun n => (hR n).2.2.2.2.2.2.2.2.1
  have c9 := fun n => (hR n).2.2.2.2.2.2.2.2.2.1
  have c10 := fun n => (hR n).2.2.2.2.2.2.2.2.2.2.1
  have c11 := fun n => (hR n).2.2.2.2.2.2.2.2.2.2.2.1
  have c12 := fun n => (hR n).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR5 := fun n => (hR n).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hDtB : ∀ n, ∀ δ T' : ℝ, 0 < δ → δ < T' → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T'),
        ∀ i, |timePartial (fun y => U n y i) z| ≤ C := by
    intro n δ T' hδ hδT'
    obtain ⟨C, hC0, hC⟩ := c10 n δ T' hδ hδT'
    exact ⟨C, hC0, fun z hz i => (hC z hz).2.2.2.2.1 i⟩
  -- energy bounds
  let B : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal
  have hA : MemLp (regUniformSpatialField a) 2 volume := lerayHopfLimit_initialField_memLp a ha.1
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hEnergySlice : ∀ n t, 0 ≤ t →
      eLpNorm (fun x => (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume ≤
        eLpNorm (regUniformSpatialField a) 2 volume := fun n t ht =>
    lerayHopfLimit_regSlice_uniformBound ρ (εseq (σ n)) (hεn n) a (U n) (Dseq n) hA
      (fun s hs => lerayHopfLimit_initialField_memLp (fun x => U n (x, s)) (hSliceMem n s hs))
      (hR5 n) t ht
  have hBslice : ∀ n t, 0 ≤ t →
      (eLpNorm (regUniformVelocitySlice (U n) t) 2 volume).toReal ≤ B := by
    intro n t ht
    have h := hEnergySlice n t ht
    rw [← lerayHopfLimit_eLpNorm_spatialField (hSliceMem n t ht)] at h
    exact ENNReal.toReal_mono hA.eLpNorm_ne_top h
  -- every positive-time slice of the limit is square integrable and solenoidal
  have hsliceU : ∀ t, 0 < t → MemLp (fun x => u (x, t)) 2 volume := by
    intro t ht
    refine lerayHopfLimit_slice_memLp_of_representative
      (fun n y => uε a ha (εseq (σ n)) (parabolicHomeomorph.symm y)) σ hσtop u t
      (fun x => by have h := hrep (x, t) ht; exact h)
      (fun n => hSliceMem n t ht.le) B hB0 (fun n => ?_) (hweakSlice t ht)
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hA.eLpNorm_ne_top (hEnergySlice n t ht.le)
  have hdivPos : ∀ t, 0 < t → ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ.partialDeriv i x = 0 := fun t ht =>
    lerayHopfLimit_divergence_of_weakSlice (fun n x => U n (x, t)) (fun x => u (x, t))
      (fun n => hSliceDiv n t ht.le) (hweakSlice t ht)
  have hdivAll : ∀ t, 0 ≤ t → IsWeakDivFreeL2 (fun x => u (x, t)) := by
    intro t ht
    rcases ht.lt_or_eq with ht' | ht'
    · exact ⟨hsliceU t ht', hdivPos t ht'⟩
    · subst ht'
      have heq : (fun x => u (x, 0)) = a := funext hu0
      rw [heq]
      exact isInJ_weakDivFree ha
  have hnorm : ∀ t (ht : 0 ≤ t), ‖(lerayHopfLimit_toLp_memLp (hdivAll t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3))‖ ≤ B := by
    intro t ht
    rcases ht.lt_or_eq with ht' | ht'
    · refine norm_le_of_tendsto_inner_and_uniform_bound (l := atTop) hB0
        (v := fun n => (lerayHopfLimit_toLp_memLp (hSliceMem n t ht)).toLp
          (fun x => (WithLp.toLp 2 (U n (x, t)) : L2Vec3)))
        (Filter.Eventually.of_forall (fun n => ?_)) ?_
      · rw [Lp.norm_toLp]
        exact ENNReal.toReal_mono hA.eLpNorm_ne_top (hEnergySlice n t ht)
      · rw [← real_inner_self_eq_norm_sq,
          lerayHopfLimit_inner_toLp_eq (hdivAll t ht).1 (hdivAll t ht).1]
        refine (hweakSlice t ht' (fun x => u (x, t)) (hsliceU t ht')).congr (fun n => ?_)
        exact (lerayHopfLimit_inner_toLp_eq (hSliceMem n t ht) (hsliceU t ht')).symm
    · subst ht'
      rw [Lp.norm_toLp]
      apply le_of_eq
      congr 1
      rw [lerayHopfLimit_eLpNorm_spatialField ha.1]
      simp only [hu0']
  -- uniform time moduli of the solenoidal pairings
  have hmod : ∀ wc : Fin 3 → Vec3 → ℝ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i)) →
      (∀ i, HasCompactSupport (wc i)) → (∀ x, ∑ i : Fin 3, spatialDeriv (wc i) i x = 0) →
      ∃ K : ℝ, ∀ s t, 0 ≤ s → 0 ≤ t →
        |(∫ x, ∑ i : Fin 3, u (x, t) i * wc i x) -
          ∫ x, ∑ i : Fin 3, u (x, s) i * wc i x| ≤ K * |t - s| := by
    intro wc hw hwc hdivw
    obtain ⟨K, _, hK⟩ := lerayHopfLimit_pairing_rhs_bound wc hw hwc B
    refine ⟨K, lerayHopfLimit_limitPairing_lipschitz
      (fun n t => ∫ x, ∑ i : Fin 3, U n (x, t) i * wc i x)
      (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * wc i x) K (fun n => ?_) ?_⟩
    · exact lerayHopfLimit_regPairing_lipschitz ρ (εseq (σ n)) (hεn n) (U n)
        (pε a ha (εseq (σ n))) (hSliceMem n) (hSliceCont n) (hSliceDiv n) (c1 n) (c2 n)
        (c3 n) (c4 n) (c5 n) (c6 n) (c7 n) (c8 n) (c9 n) (hDtB n) (c12 n) B (hBslice n)
        wc hw hwc hdivw K hK
    · intro t ht
      have hW : MemLp (fun x i => wc i x) 2 volume :=
        MemLp.of_eval (fun i => lerayHopfLimit_memLp_two_of_compact (hw i).continuous (hwc i))
      rcases ht.lt_or_eq with ht' | ht'
      · exact hweakSlice t ht' (fun x i => wc i x) hW
      · subst ht'
        have hcongr : ∀ n, ∫ x, ∑ i : Fin 3, U n (x, 0) i * wc i x =
            ∫ x, ∑ i : Fin 3, regUniformMollifiedInitial ρ (εseq (σ n)) (hεn n) a x i *
              wc i x := by
          intro n
          refine integral_congr_ae ((hSlice0 n).mono (fun x hx => ?_))
          change ∑ i : Fin 3, U n (x, 0) i * wc i x = _
          rw [show U n (x, 0) = regUniformMollifiedInitial ρ (εseq (σ n)) (hεn n) a x from hx]
        have h := lerayHopfLimit_mollifiedInitial_pairing_tendsto ρ ha.1
          (fun n => εseq (σ n)) hεn hεsub (fun x i => wc i x) hW
        simp only [hcongr, hu0']
        exact h
  have hLH2 : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * w x i) (Icc 0 T) :=
    lerayHopfLimit_weakContinuity T u B hB0 hdivAll hnorm hmod
  -- the energy inequality at every positive time, in real form
  have hEreal : ∀ t₀, 0 < t₀ →
      (∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j ^ 2) ≤
      ∑ i : Fin 3, ∫ x, a x i ^ 2 := by
    intro t₀ ht₀
    obtain ⟨_, _, _, hDuL2', _, hDweak', _⟩ := hslabAll t₀ ht₀
    refine lerayHopfLimit_energy_real t₀ U u Du a (fun n => hSliceMem n t₀ ht₀.le)
      (hsliceU t₀ ht₀) (hweakSlice t₀ ht₀ _ (hsliceU t₀ ht₀)) (fun n i j => ?_)
      (fun i j => (hDuL2'.eval i).eval j)
      (fun i j => hDweak' i j _ ((hDuL2'.eval i).eval j)) ha.1 (fun n => ?_)
    · exact lerayHopfLimit_aestronglyMeasurable_of_slabs ht₀ (fun δ hδ hδt =>
        ((c11 n δ t₀ hδ hδt).2.1 i j).aestronglyMeasurable)
    · rw [hR5 n t₀ ht₀.le]
      exact pow_le_pow_left₀ bot_le
        (regMollifyVector_eLpNorm_two_le ρ (εseq (σ n)) (hεn n) hA) 2
  -- the weak momentum equation
  have hU3conv : Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (𝓝 0) := by
    have h := hUconvq 3 (by norm_num) (by norm_num)
    rw [ENNReal.ofReal_ofNat] at h
    exact h
  have hLH3 := lerayHopfLimit_momentum T hT U
    (fun n => regUniformMollifiedVelocity ρ (εseq (σ n)) (hεn n) (U n))
    (fun n => pε a ha (εseq (σ n))) u Du hUL3 hJL3 huL3 hU3conv hJconv hDuL2 hDweak
    (fun δ hδ hδT n i j => (c11 n δ T hδ hδT).2.1 i j)
    (fun n φ hφ => hregMomentum a ha (εseq (σ n)) (hεn n) φ hφ)
  -- the measurability, energy, gradient and divergence clauses
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lerayHopfLimit_LH1_of_limitData T a ha ρ εseq σ hεn u Du
    U Dseq huAE hDuAE huL2 hDuL2
    (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hgrad)
    hSliceDiv hweakSlice hSliceMem hR5
  refine ⟨hT, ha, h1, h2, h3, h4, h5, h6, hLH2, hLH3, ?_, ?_⟩
  · intro t₀ ht₀
    rcases ht₀.1.lt_or_eq with hpos | hzero
    · obtain ⟨_, _, _, hDuL2', _⟩ := hslabAll t₀ hpos
      exact lerayHopfLimit_energy_ennreal t₀ u Du a (hsliceU t₀ hpos)
        (fun i j => (hDuL2'.eval i).eval j) ha.1 (hEreal t₀ hpos)
    · subst hzero
      rw [Ioo_self, show spaceTimeSet (Set.univ : Set Vec3) (∅ : Set ℝ) = ∅ from
        Set.prod_empty, Measure.restrict_empty, lintegral_zero_measure, add_zero]
      simp only [hu0']
      exact le_rfl
  · refine lerayHopfLimit_initialTrace T hT u a hu0' ha.1 hsliceU (fun t ht _ => ?_) (hLH2 a ha.1)
    have h := hEreal t ht
    have hG : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), Du z i j ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        integral_nonneg (fun z => sq_nonneg _)))
    linarith only [h, hG]

end CKN.Leray

end
