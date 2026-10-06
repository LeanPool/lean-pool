/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalTimeLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalPairings
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Leray.PressureLimitLeray
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayAssemblyHopfData
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayAssemblyMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayAssemblyEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumSupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFluxProduct
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeightedGradientMatrix
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsGlobalLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution

/-!
# Leray Assembly Contracts

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The direct limiting argument for `thm:leray`, with the regularized
identities and convergence statements as explicit inputs. -/
theorem lerayExistence_of_limits
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
    (hregLocalEnergy : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε) (ψ : ParabolicPoint → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (uε a ha ε)
            (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z) z * ψ z =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (uε a ha ε z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (uε a ha ε z)) ^ (2 : ℕ) *
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                    (uε a ha ε) z i +
                2 * pε a ha ε z * uε a ha ε z i) *
                spatialPartial ψ i z)
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
                uε a ha (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z))
    (hpressureLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0))
      (σ : ℕ → ℕ) (u : ParabolicPoint → Vec3)
      (hσ : StrictMono σ) (hσtop : Tendsto σ atTop atTop)
      (hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0))
      (hUseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (uε a ha (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0))
      (hJseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1)
            (uε a ha (εseq (σ n))) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0)),
      ∃ p : ParabolicPoint → ℝ,
        ∀ T : ℝ, 0 < T →
          let μ : Measure (Vec3 × ℝ) :=
            (volume : Measure (Vec3 × ℝ)).restrict
              (CKN.Leray.lerayPressureLimitSlab T)
          let uST : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
          let pST : Vec3 × ℝ → ℝ := fun z => p (parabolicHomeomorph.symm z)
          let pseq : ℕ → Vec3 × ℝ → ℝ := fun n z =>
            pε a ha (εseq (σ n)) (parabolicHomeomorph.symm z)
          ∃ hu : MemLp uST 3 μ,
            MemLp pST (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
            pST =ᵐ[μ] CKN.Leray.lerayProductPressureOnSlab T uST uST hu hu ∧
            Tendsto (fun n => eLpNorm (pseq n - pST)
              (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0))
    (hhopfLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0)),
      let hlim := hlerayLimit a ha εseq hseq hεseq
      let _σ := Classical.choose hlim
      let hlim₁ := Classical.choose_spec hlim
      let u := Classical.choose hlim₁
      let hlim₂ := Classical.choose_spec hlim₁
      let Du := Classical.choose hlim₂
      ∀ T : ℝ, 0 < T → IsLerayHopfSolution T a u Du) :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ q : ℝ, 5 / 2 < q →
          IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p
            (0 : ParabolicPoint → Vec3) := by
  intro a ha
  let εseq : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  have hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1 := by
    intro n
    constructor
    · dsimp [εseq]
      positivity
    · dsimp [εseq]
      have hden : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
      simpa only [ge_iff_le, one_div, ne_eq, one_ne_zero, not_false_eq_true, div_self] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden)
  have hεseq : Tendsto εseq atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let hlim := hlerayLimit a ha εseq hseq hεseq
  let σ := Classical.choose hlim
  let hlim₁ := Classical.choose_spec hlim
  let u := Classical.choose hlim₁
  let hlim₂ := Classical.choose_spec hlim₁
  let Du := Classical.choose hlim₂
  let hlimData := Classical.choose_spec hlim₂
  have hσ : StrictMono σ := hlimData.1
  have hσtop : Tendsto σ atTop atTop := hlimData.2.1
  have hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0) :=
    hlimData.2.2.1
  have hlimitOn (T : ℝ) (hT : 0 < T) := hlimData.2.2.2.2.1 T hT
  have hUseqLthree : ∀ T : ℝ, 0 < T →
      Tendsto (fun n => eLpNorm
        (uε a ha (εseq (Classical.choose hlim n)) -
          Classical.choose (Classical.choose_spec hlim))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0) := by
    intro T hT
    rcases hlimitOn T hT with
      ⟨_, _, _, _, _, _, hLq, _, _, _, _, _, _⟩
    have h := hLq 3 (by norm_num) (by norm_num)
    change Tendsto (fun n => eLpNorm
      (uε a ha (εseq (Classical.choose hlim n)) -
        Classical.choose (Classical.choose_spec hlim))
      (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
      ) atTop (nhds 0) at h
    simpa only [parabolicHomeomorph_symm_apply, measurableSet_Ioi, ae_restrict_eq,
      eventually_all, Prod.mk.eta, Prod.forall, exists_and_left, exists_and_right,
      ENNReal.ofReal_ofNat] using h
  have hJseqLthree : ∀ T : ℝ, 0 < T →
      Tendsto (fun n => eLpNorm
        (CKN.Leray.regUniformMollifiedVelocity ρ
          (εseq (Classical.choose hlim n))
          (by exact (hseq (Classical.choose hlim n)).1)
          (uε a ha (εseq (Classical.choose hlim n))) -
          Classical.choose (Classical.choose_spec hlim))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0) := by
    intro T hT
    rcases hlimitOn T hT with
      ⟨_, _, _, _, _, _, _, _, _, _, hJconv, _, _⟩
    simpa only [parabolicHomeomorph_symm_apply, measurableSet_Ioi, ae_restrict_eq,
      eventually_all, Prod.mk.eta, Prod.forall, exists_and_left, exists_and_right,
      ENNReal.ofReal_ofNat] using hJconv
  obtain ⟨p, hpLimit⟩ := hpressureLimit a ha εseq hseq hεseq
    (Classical.choose hlim) (Classical.choose (Classical.choose_spec hlim))
    hσ hσtop hεsubseq hUseqLthree hJseqLthree
  have hglobal : IsGlobalLerayHopfSolution a u Du := by
    intro T hT
    exact hhopfLimit a ha εseq hseq hεseq T hT
  have hcanonicalPressure (T : ℝ) (hT : 0 < T) :
      ∃ hu : MemLp (fun z : Vec3 × ℝ =>
          u (parabolicHomeomorph.symm z)) 3
          ((volume : Measure (Vec3 × ℝ)).restrict
            (CKN.Leray.lerayPressureLimitSlab T)),
        MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
          (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict
            (CKN.Leray.lerayPressureLimitSlab T)) ∧
        (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)) =ᵐ[
          (volume : Measure (Vec3 × ℝ)).restrict
            (CKN.Leray.lerayPressureLimitSlab T)]
          CKN.Leray.lerayProductPressureOnSlab T
            (fun z => u (parabolicHomeomorph.symm z))
            (fun z => u (parabolicHomeomorph.symm z)) hu hu := by
    rcases hpLimit T hT with ⟨hu, hp, hcanonical, _⟩
    exact ⟨hu, hp, hcanonical⟩
  have hpressureLp (T : ℝ) (hT : 0 < T) :
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rcases hcanonicalPressure T hT with ⟨hu, hp, hcanonical⟩
    exact CKN.Leray.lerayAssembly_productSlab_memLp_to_parabolic hp
  have hdata (q : ℝ) (hq : 5 / 2 < q) :=
    CKN.Leray.lerayAssembly_hopfData hglobal hpressureLp hq
  have hdivergence :
      ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (Set.univ : Set Vec3) (Ioi 0) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
    intro ψ hψ
    exact CKN.Leray.lerayAssembly_hopfDivergence
      hglobal ψ hψ
  refine ⟨u, Du, p, hglobal, ?_⟩
  intro q hq
  unfold CKN.IsSuitableWeakSolution
  rcases hdata q hq with
    ⟨hopenSpace, hopenTime, hord, hq', hforce, hdataLocal⟩
  have hmomentum : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j *
              spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, Du z i j *
              spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i = 0 := by
    intro φ hφ
    let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
    have hK : IsCompact K := isCompact_tsupport_parabolic hφ.2.1
    have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
      tsupport_parabolic_subset_spaceTimeSet hφ
    obtain ⟨Ω', J, hbox, hKbox⟩ :=
      caccioppoli_localBox_of_compact_subset
        isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
    obtain ⟨δ, T, hδ, hδT, hJδT⟩ :=
      CKN.Leray.lerayAssembly_localBox_time_bounds hbox
    have hT : 0 < T := lt_trans hδ hδT
    have hJT : J ⊆ Ioo 0 T := by
      intro t ht
      exact ⟨lt_trans hδ (hJδT ht).1, (hJδT ht).2⟩
    let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
    let U : ℕ → ParabolicPoint → Vec3 :=
      fun n => uε a ha (εseq (σ n))
    let Jv : ℕ → ParabolicPoint → Vec3 := fun n =>
      CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
        (hseq (σ n)).1 (U n)
    let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 :=
      fun n z i j => spatialPartial (fun y => U n y i) j z
    let Pseq : ℕ → ParabolicPoint → ℝ :=
      fun n => pε a ha (εseq (σ n))
    have hslab := hlimitOn T hT
    rcases hslab with
      ⟨_, _, _, hDu2, _, hweak, hLq, hUL3, hJL3, huL3, hJL3conv, _, _⟩
    have hμLE : μ ≤ volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      Measure.restrict_mono_set (volume : Measure ParabolicPoint)
        (Set.prod_mono (Set.subset_univ (Ω' : Set Vec3)) hJT)
    have hUconv : Tendsto (fun n => eLpNorm (U n - u)
        (ENNReal.ofReal (3 : ℝ)) μ)
        atTop (nhds 0) := by
      exact CKN.Leray.lerayAssembly_strongConv_localBox hJT U u
        (hUseqLthree T hT)
    have hJconv : Tendsto (fun n => eLpNorm (Jv n - u)
        (ENNReal.ofReal (3 : ℝ)) μ)
        atTop (nhds 0) := by
      exact CKN.Leray.lerayAssembly_strongConv_localBox hJT Jv u
        (hJseqLthree T hT)
    have hULocal (n : ℕ) : MemLp (U n) 3 μ := by
      exact (hUL3 n).mono_measure hμLE
    have hJLocal (n : ℕ) : MemLp (Jv n) 3 μ := by
      exact (hJL3 n).mono_measure hμLE
    have huLocal : MemLp u 3 μ := by
      exact huL3.mono_measure hμLE
    let : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
    have hμδT : μ ≤ volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
      Measure.restrict_mono_set (volume : Measure ParabolicPoint)
        (Set.prod_mono (Set.subset_univ (Ω' : Set Vec3)) hJδT)
    have hR4 (n : ℕ) := by
      rcases hregularised a ha (εseq (σ n)) (hseq (σ n)).1 with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hR4, _, _, _⟩
      exact hR4 δ T hδ hδT
    have hDLocal (n : ℕ) (i j : Fin 3) :
        MemLp (fun z => Dseq n z i j) 2 μ := by
      have h := (hR4 n).2.1 i j
      exact h.mono_measure hμδT
    have hDuLocal (i j : Fin 3) :
        MemLp (fun z => Du z i j) 2 μ := by
      have h := ((memLp_pi_iff.mp ((memLp_pi_iff.mp hDu2) i)) j)
      exact h.mono_measure hμLE
    have hPSeqLocalTwo (n : ℕ) : MemLp (Pseq n) 2 μ := by
      have h := (hR4 n).2.2.2.2
      exact h.mono_measure hμδT
    have hPSeqLocal (n : ℕ) :
        MemLp (Pseq n) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
      exact (hPSeqLocalTwo n).mono_exponent (by norm_num)
    have hpLocal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
      exact (hpressureLp T hT).mono_measure hμLE
    have hPconv : Tendsto (fun n => eLpNorm (Pseq n - p)
        (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
      rcases hpLimit T hT with ⟨huST, hpST, _, hpConvST⟩
      exact CKN.Leray.lerayAssembly_pressureConv_localBox hbox hJT
        Pseq p hPSeqLocalTwo hpST hpConvST
    have hWeakLocal (i j : Fin 3) : Tendsto
        (fun n => ∫ z in spaceTimeSet Ω' J,
          Dseq n z i j * spatialPartial (fun w => φ w i) j z) atTop
        (nhds (∫ z in spaceTimeSet Ω' J,
          Du z i j * spatialPartial (fun w => φ w i) j z)) := by
      let w : ParabolicPoint → ℝ :=
        fun z => spatialPartial (fun y => φ y i) j z
      have hwzeroK : ∀ z ∉ K, w z = 0 := by
        intro z hz
        apply spatialPartial_eq_zero_off_tsupport
        intro hmem
        apply hz
        change z ∈ tsupport (show ParabolicPoint → Vec3 from φ)
        rw [tsupport_parabolic_eq]
        exact (tsupport_component_subset (V := ℝ) φ i
          (fun _ h => by rw [h]; rfl)) hmem
      have hwzero : ∀ z ∉ spaceTimeSet Ω' J, w z = 0 := by
        intro z hz
        exact hwzeroK z (fun hmem => hz (hKbox hmem))
      have hwcont : Continuous w :=
        (spatialPartial_contDiff (component_mem_spaceTimeTestFunction hφ i).1 j).continuous.comp
          parabolicHomeomorph.continuous
      have hwsupport : Function.support w ⊆ K := by
        intro z hz
        by_contra hzK
        exact hz (hwzeroK z hzK)
      have hwcompact : HasCompactSupport w :=
        HasCompactSupport.of_support_subset_isCompact hK hwsupport
      have hw2 : MemLp w 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
        (hwcont.memLp_of_hasCompactSupport hwcompact).restrict _
      exact CKN.Leray.lerayAssembly_weakConv_localBox hJT
        (fun n z => Dseq n z i j) (fun z => Du z i j) w hwzero
        (hweak i j w hw2)
    have hUconvThree : Tendsto (fun n => eLpNorm (U n - u) 3 μ)
        atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_ofNat] using hUconv
    have hJconvThree : Tendsto (fun n => eLpNorm (Jv n - u) 3 μ)
        atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_ofNat] using hJconv
    have hAconv := CKN.Leray.lerayHopfLimit_linearTerm_tendsto μ
      U u hULocal hUconvThree
      (fun i z => timePartial (fun w => φ w i) z)
      (fun i => stability_timePartial_memLp_top φ hφ i)
    have hBconv := CKN.Leray.lerayHopfLimit_advectiveTerm_tendsto μ
      U Jv u hULocal hJLocal huLocal hUconvThree hJconvThree
      (fun i j z => spatialPartial (fun w => φ w i) j z)
      (fun i j => stability_spatialPartial_memLp_top φ hφ i j)
    have hCseqInt (n : ℕ) (i j : Fin 3) : Integrable
        (fun z : ParabolicPoint => Dseq n z i j *
          spatialPartial (fun w => φ w i) j z) μ :=
      stability_integrable_mul_bounded_test μ (by norm_num)
        (hDLocal n i j) (stability_spatialPartial_memLp_top φ hφ i j)
    have hClimInt (i j : Fin 3) : Integrable
        (fun z : ParabolicPoint => Du z i j *
          spatialPartial (fun w => φ w i) j z) μ :=
      stability_integrable_mul_bounded_test μ (by norm_num)
        (hDuLocal i j) (stability_spatialPartial_memLp_top φ hφ i j)
    have hCconv : Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          Dseq n z i j * spatialPartial (fun w => φ w i) j z) atTop
        (nhds (∫ z in spaceTimeSet Ω' J,
          ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun w => φ w i) j z)) := by
      apply stability_tendsto_integral_finsetSum μ Finset.univ
        (fun n i z => ∑ j : Fin 3,
          Dseq n z i j * spatialPartial (fun w => φ w i) j z)
        (fun i z => ∑ j : Fin 3,
          Du z i j * spatialPartial (fun w => φ w i) j z)
      · intro n i _
        exact integrable_finsetSum Finset.univ (fun j _ => hCseqInt n i j)
      · intro i _
        exact integrable_finsetSum Finset.univ (fun j _ => hClimInt i j)
      · intro i _
        apply stability_tendsto_integral_finsetSum μ Finset.univ
          (fun n j z => Dseq n z i j * spatialPartial (fun w => φ w i) j z)
          (fun j z => Du z i j * spatialPartial (fun w => φ w i) j z)
          (fun n j _ => hCseqInt n i j) (fun j _ => hClimInt i j)
          (fun j _ => hWeakLocal i j)
    have hPconvInt : Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
        Pseq n z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z) atTop
        (nhds (∫ z in spaceTimeSet Ω' J,
          p z * ∑ i : Fin 3,
            spatialPartial (fun w => φ w i) i z)) := by
      have h := stability_tendsto_integral_mul_test_of_LthreeHalves μ
        Pseq p (fun z => ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z)
        (fun n => by simpa only [CKN.ofReal_threeHalves] using hPSeqLocal n)
        (stability_testDivergence_memLp_top φ hφ)
        (by simpa only [CKN.ofReal_threeHalves] using hPconv)
      have heqN (n : ℕ) :
          (∫ z, (∑ i : Fin 3,
            spatialPartial (fun w => φ w i) i z) * Pseq n z ∂μ) =
          ∫ z, Pseq n z * ∑ i : Fin 3,
            spatialPartial (fun w => φ w i) i z ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      have heqP :
          (∫ z, (∑ i : Fin 3,
            spatialPartial (fun w => φ w i) i z) * p z ∂μ) =
          ∫ z, p z * ∑ i : Fin 3,
            spatialPartial (fun w => φ w i) i z ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      simpa only [heqN, heqP] using h
    have hASeqInt (n : ℕ) : Integrable
        (fun z : ParabolicPoint => ∑ i : Fin 3,
          U n z i * timePartial (fun w => φ w i) z) μ :=
      integrable_finsetSum Finset.univ (fun i _ =>
        stability_integrable_mul_bounded_test μ (by norm_num)
          ((memLp_pi_iff.mp (hULocal n)) i)
          (stability_timePartial_memLp_top φ hφ i))
    have hALimInt : Integrable
        (fun z : ParabolicPoint => ∑ i : Fin 3,
          u z i * timePartial (fun w => φ w i) z) μ :=
      integrable_finsetSum Finset.univ (fun i _ =>
        stability_integrable_mul_bounded_test μ (by norm_num)
          ((memLp_pi_iff.mp huLocal) i)
          (stability_timePartial_memLp_top φ hφ i))
    let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
      have hreal : Real.HolderTriple 3 3 (3 / 2) :=
        ⟨by norm_num, by norm_num, by norm_num⟩
      simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
        hreal.ennrealOfReal
    have hOneThreeHalves : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
      rw [← CKN.ofReal_threeHalves]
      simpa using ENNReal.ofReal_le_ofReal
        (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hBSeqTermInt (n : ℕ) (i j : Fin 3) : Integrable
        (fun z : ParabolicPoint => U n z i * Jv n z j *
          spatialPartial (fun w => φ w i) j z) μ := by
      have hprod : MemLp (fun z : ParabolicPoint => U n z i * Jv n z j)
          (3 / 2 : ℝ≥0∞) μ := by
        have h : MemLp
            ((fun z : ParabolicPoint => U n z i) *
              (fun z : ParabolicPoint => Jv n z j))
            (3 / 2 : ℝ≥0∞) μ :=
          ((memLp_pi_iff.mp (hULocal n)) i).mul
            ((memLp_pi_iff.mp (hJLocal n)) j)
        exact h
      exact stability_integrable_mul_bounded_test μ hOneThreeHalves hprod
        (stability_spatialPartial_memLp_top φ hφ i j)
    have hBLimTermInt (i j : Fin 3) : Integrable
        (fun z : ParabolicPoint => u z i * u z j *
          spatialPartial (fun w => φ w i) j z) μ := by
      have hprod : MemLp (fun z : ParabolicPoint => u z i * u z j)
          (3 / 2 : ℝ≥0∞) μ := by
        have h : MemLp
            ((fun z : ParabolicPoint => u z i) *
              (fun z : ParabolicPoint => u z j))
            (3 / 2 : ℝ≥0∞) μ :=
          ((memLp_pi_iff.mp huLocal) i).mul
            ((memLp_pi_iff.mp huLocal) j)
        exact h
      exact stability_integrable_mul_bounded_test μ hOneThreeHalves hprod
        (stability_spatialPartial_memLp_top φ hφ i j)
    have hBSeqInt (n : ℕ) : Integrable
        (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
          U n z i * Jv n z j * spatialPartial (fun w => φ w i) j z) μ :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hBSeqTermInt n i j))
    have hBLimInt : Integrable
        (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
          u z i * u z j * spatialPartial (fun w => φ w i) j z) μ :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hBLimTermInt i j))
    have hCSeqInt (n : ℕ) : Integrable
        (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
          Dseq n z i j * spatialPartial (fun w => φ w i) j z) μ :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hCseqInt n i j))
    have hCLimInt : Integrable
        (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
          Du z i j * spatialPartial (fun w => φ w i) j z) μ :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hClimInt i j))
    have hPSeqInt (n : ℕ) : Integrable
        (fun z : ParabolicPoint => Pseq n z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z) μ :=
      stability_integrable_mul_bounded_test μ (by norm_num)
        (hPSeqLocal n) (stability_testDivergence_memLp_top φ hφ)
    have hPLimInt : Integrable
        (fun z : ParabolicPoint => p z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z) μ :=
      stability_integrable_mul_bounded_test μ (by norm_num)
        hpLocal (stability_testDivergence_memLp_top φ hφ)
    have hregN (n : ℕ) :
        (∫ z in spaceTimeSet Ω' J,
          (-(∑ i : Fin 3,
              U n z i * timePartial (fun w => φ w i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                U n z i * Jv n z j *
                  spatialPartial (fun w => φ w i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Dseq n z i j * spatialPartial (fun w => φ w i) j z
            - Pseq n z * ∑ i : Fin 3,
                spatialPartial (fun w => φ w i) i z) = 0 := by
      have h := hregMomentum a ha (εseq (σ n)) (hseq (σ n)).1 φ hφ
      rw [CKN.Leray.lerayAssembly_regMomentum_localBox φ hφ hKbox
        (U n) (Jv n) (Dseq n) (Pseq n)] at h
      have hpoint (z : ParabolicPoint) :
          (∑ i : Fin 3, ∑ j : Fin 3,
            U n z i * Jv n z j *
              spatialPartial (fun w => φ w i) j z) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            Jv n z j * U n z i *
              spatialPartial (fun w => φ w i) j z := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp_rw [hpoint]
      exact h
    have hlocal := CKN.Leray.lerayAssembly_momentum_four_terms μ
      (fun n z => ∑ i : Fin 3,
        U n z i * timePartial (fun w => φ w i) z)
      (fun n z => ∑ i : Fin 3, ∑ j : Fin 3,
        U n z i * Jv n z j * spatialPartial (fun w => φ w i) j z)
      (fun n z => ∑ i : Fin 3, ∑ j : Fin 3,
        Dseq n z i j * spatialPartial (fun w => φ w i) j z)
      (fun n z => Pseq n z * ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z)
      (fun z => ∑ i : Fin 3,
        u z i * timePartial (fun w => φ w i) z)
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * spatialPartial (fun w => φ w i) j z)
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * spatialPartial (fun w => φ w i) j z)
      (fun z => p z * ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z)
      hASeqInt hBSeqInt hCSeqInt hPSeqInt
      hALimInt hBLimInt hCLimInt hPLimInt
      hAconv hBconv hCconv hPconvInt hregN
    rw [stability_momentum_integral_eq_localBox φ hφ hKbox u Du p]
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
      using hlocal
  have henergy : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (Set.univ : Set Vec3) (Ioi 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          vec3EuclideanNorm (u z) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3,
                spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ (2 : ℕ) + 2 * p z) *
                ∑ i : Fin 3, u z i * spatialPartial ψ i z
            + 2 * (∑ i : Fin 3,
              (0 : ParabolicPoint → Vec3) z i * u z i) * ψ z := by
    intro ψ hψ hψpos
    let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
    have hK : IsCompact K := isCompact_tsupport_parabolic hψ.2.1
    have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
      tsupport_parabolic_subset_spaceTimeSet hψ
    obtain ⟨Ω', J, hbox, hKbox⟩ :=
      caccioppoli_localBox_of_compact_subset
        isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
    obtain ⟨δ, T, hδ, hδT, hJδT⟩ :=
      CKN.Leray.lerayAssembly_localBox_time_bounds hbox
    have hT : 0 < T := lt_trans hδ hδT
    have hJT : J ⊆ Ioo 0 T := by
      intro t ht
      exact ⟨lt_trans hδ (hJδT ht).1, (hJδT ht).2⟩
    let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
    let : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
    let U : ℕ → ParabolicPoint → Vec3 :=
      fun n => uε a ha (εseq (σ n))
    let Jv : ℕ → ParabolicPoint → Vec3 := fun n =>
      CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
        (hseq (σ n)).1 (U n)
    let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 :=
      fun n z i j => spatialPartial (fun y => U n y i) j z
    let Pseq : ℕ → ParabolicPoint → ℝ :=
      fun n => pε a ha (εseq (σ n))
    have hμLE : μ ≤ volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      Measure.restrict_mono_set (volume : Measure ParabolicPoint)
        (Set.prod_mono (Set.subset_univ (Ω' : Set Vec3)) hJT)
    rcases hlimitOn T hT with
      ⟨_, _, _, hDu2, _, hweak, hLq, hUL3, hJL3, huL3, hJL3conv, _, _⟩
    have hUconv : Tendsto (fun n => eLpNorm (U n - u) 3 μ)
        atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_ofNat] using
        (CKN.Leray.lerayAssembly_strongConv_localBox hJT U u
          (hUseqLthree T hT))
    have hJconv : Tendsto (fun n => eLpNorm (Jv n - u) 3 μ)
        atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_ofNat] using
        (CKN.Leray.lerayAssembly_strongConv_localBox hJT Jv u
          (hJseqLthree T hT))
    have hULocal (n : ℕ) : MemLp (U n) 3 μ :=
      (hUL3 n).mono_measure hμLE
    have hJLocal (n : ℕ) : MemLp (Jv n) 3 μ :=
      (hJL3 n).mono_measure hμLE
    have huLocal : MemLp u 3 μ := huL3.mono_measure hμLE
    have hDuLocal : MemLp Du 2 μ := hDu2.mono_measure hμLE
    have hμδT : μ ≤ volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
      Measure.restrict_mono_set (volume : Measure ParabolicPoint)
        (Set.prod_mono (Set.subset_univ (Ω' : Set Vec3)) hJδT)
    have hR4 (n : ℕ) := by
      rcases hregularised a ha (εseq (σ n)) (hseq (σ n)).1 with
        ⟨_, _, _, _, _, _, _, _, _, _, _, hR4, _, _, _⟩
      exact hR4 δ T hδ hδT
    have hDSeqLocal (n : ℕ) : MemLp (Dseq n) 2 μ := by
      apply memLp_pi_iff.mpr
      intro i
      apply memLp_pi_iff.mpr
      intro j
      exact ((hR4 n).2.1 i j).mono_measure hμδT
    have hPSeqLocalTwo (n : ℕ) : MemLp (Pseq n) 2 μ :=
      ((hR4 n).2.2.2.2).mono_measure hμδT
    have hpLocal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
      (hpressureLp T hT).mono_measure hμLE
    have hPconv : Tendsto (fun n => eLpNorm (Pseq n - p)
        (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
      rcases hpLimit T hT with ⟨_, hpST, _, hpConvST⟩
      exact CKN.Leray.lerayAssembly_pressureConv_localBox hbox hJT
        Pseq p hPSeqLocalTwo hpST hpConvST
    have hWeakLocal (i j : Fin 3) (w : ParabolicPoint → ℝ)
        (hw : MemLp w 2 μ) :
        Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
          Dseq n z i j * w z) atTop
        (nhds (∫ z in spaceTimeSet Ω' J,
          Du z i j * w z)) :=
      CKN.Leray.lerayAssembly_weakConv_localBox_all hbox hJT
        (fun n z => Dseq n z i j) (fun z => Du z i j)
        (hweak i j) w hw
    have hreg (n : ℕ) := hregLocalEnergy a ha
      (εseq (σ n)) (hseq (σ n)).1 ψ hψ
    have hlocal := CKN.Leray.lerayAssembly_localEnergy_limit
      hbox U Jv Dseq Pseq u Du p ψ hψ hKbox hψpos hULocal hJLocal
      huLocal hUconv hJconv hDSeqLocal hDuLocal hWeakLocal
      (fun n => (hPSeqLocalTwo n).mono_exponent (by norm_num))
      hpLocal hPconv hreg
    rw [stability_energy_gradient_integral_eq_localBox ψ hψ hKbox u Du,
      stability_energy_rhs_integral_eq_localBox ψ hψ hKbox u p]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      mul_zero, add_zero]
    convert hlocal using 1
    apply integral_congr_ae
    filter_upwards [] with z
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact ⟨hopenSpace, hopenTime, hord, hq', hforce, hdataLocal,
    hdivergence, hmomentum, henergy⟩

end CKN

end
