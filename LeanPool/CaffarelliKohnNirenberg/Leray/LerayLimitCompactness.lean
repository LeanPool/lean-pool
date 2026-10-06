/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMain
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientFiber

/-!
# Leray Limit Compactness

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)



theorem lerayLimit_local_compactness
(hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
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
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
(hregEquicontinuity : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
  (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
  (C : Set Vec3) (_hC : IsCompact C) (_hCU : C ⊆ (Set.univ : Set Vec3))
  (s₀ s₁ : ℝ) (_hs₀s₁ : Icc s₀ s₁ ⊆ Ioi (0 : ℝ))
  (w : Vec3 → L2Vec3) (_hw : ContDiff ℝ (⊤ : ℕ∞) w)
  (_hwc : HasCompactSupport w) (_hws : tsupport w ⊆ C),
  ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
    ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ →
      |(∫ x : Vec3, ∑ i : Fin 3,
          uε a ha (εseq n) (x, t) i * w x i ∂volume) -
        (∫ x : Vec3, ∑ i : Fin 3,
          uε a ha (εseq n) (x, s) i * w x i ∂volume)| ≤
        A * dist t s + B * (dist t s) ^ θ)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1) :
    let Ubar : ℕ → Vec3 × ℝ → Vec3 := fun n z =>
      lerayLimitPiecewise
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ)))
        (fun q => uε a ha (εseq n) (parabolicHomeomorph.symm q))
        (fun q => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a q.1)
        z
    let Dbar : ℕ → Vec3 × ℝ → Fin 3 → Vec3 := fun n z i j =>
      lerayLimitPiecewise
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ)))
        (fun q k l => spatialPartial
          (fun y => uε a ha (εseq n) y k) l q)
        (fun _ _ _ => 0) (parabolicHomeomorph.symm z) i j
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ v : Vec3 × ℝ → Vec3, ∃ g : Vec3 × ℝ → CompactnessGradientFiber,
      Measurable v ∧ Measurable g ∧
      (∀ z : Vec3 × ℝ,
        v z = compactnessMollifiedLimit Ubar σ z) ∧
      (∀ t : Set.Ioi (0 : ℝ), ∀ C : Set Vec3, IsCompact C →
        C ⊆ (Set.univ : Set Vec3) →
        ∃ hs : ∀ k, MemLp
          (fun x : Vec3 => (WithLp.toLp 2
            (Ubar (σ k) (x, t.1)) : L2Vec3))
          2 (volume.restrict C),
        ∃ hl : MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (v (x, t.1)) : L2Vec3))
          2 (volume.restrict C),
        ∀ w : Lp L2Vec3 2 (volume.restrict C),
          Tendsto (fun k => inner ℝ ((hs k).toLp
            (fun x => (WithLp.toLp 2
              (Ubar (σ k) (x, t.1)) : L2Vec3))) w)
            atTop (nhds (inner ℝ (hl.toLp
              (fun x => (WithLp.toLp 2 (v (x, t.1)) : L2Vec3))) w))) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q →
        Q ⊆ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        Tendsto (fun k => eLpNorm
          ((fun z : Vec3 × ℝ => (WithLp.toLp 2 (Ubar (σ k) z) : L2Vec3)) -
           (fun z : Vec3 × ℝ => (WithLp.toLp 2
            (v z) : L2Vec3))) 2 (volume.restrict Q)) atTop (nhds 0)) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q →
        Q ⊆ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        ∃ hs : ∀ k, MemLp
          (fun z : Vec3 × ℝ => toCompactnessGradientFiber
            (Dbar (σ k) z))
          2 (volume.restrict Q),
        ∃ hl : MemLp g 2 (volume.restrict Q),
        ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict Q),
          Tendsto (fun k => inner ℝ ((hs k).toLp
            (fun z => toCompactnessGradientFiber
              (Dbar (σ k) z))) w) atTop
            (nhds (inner ℝ (hl.toLp g) w))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => v (x, t) i)
          (fun x j => (WithLp.ofLp (g (x, t) i)) j)) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
        ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
        ∀ M : ℝ≥0∞, M < ⊤ →
          (∀ n t, t ∈ Icc b₁ b₂ →
            (∫⁻ x in C, ENNReal.ofReal
              (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ) ∂volume) ≤ M) →
          ∀ t ∈ Icc b₁ b₂,
            (∫⁻ x in C, ENNReal.ofReal
              (vec3EuclideanNorm (v (x, t))) ^ (2 : ℝ) ∂volume) ≤ M) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
        ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
        ∀ G : ℝ≥0∞, G < ⊤ →
          (∀ n,
            (∫⁻ t in Icc b₁ b₂, ∫⁻ x in C,
              ENNReal.ofReal (spatialGradientSq (Ubar n) (Dbar n) (x,t))
                ∂volume ∂volume) ≤ G) →
          (∫⁻ t in Icc b₁ b₂, ∫⁻ x in C,
            ENNReal.ofReal (spatialGradientSq
              (fun _ => (0 : Vec3))
              (fun z i j => (WithLp.ofLp (g z i)) j) (x,t))
            ∂volume ∂volume) ≤ G) := by
  classical
  let P : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  let U : ℕ → ParabolicPoint → Vec3 := fun n => uε a ha (εseq n)
  let D : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
    spatialPartial (fun y => U n y i) j z
  let Ubar : ℕ → ParabolicPoint → Vec3 := fun n =>
    lerayLimitPiecewise P (U n)
      (fun z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1)
  let Dbar : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n =>
    lerayLimitPiecewise P (D n) (fun _ => 0)
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hData (n : ℕ) :=
    lerayLimit_regularised_basic_data (ρ := ρ) (uε := uε) (pε := pε)
      (hregularised := hregularised) a ha (εseq n) (hseq n).1
  have hUpos (n : ℕ) (x : Vec3) (t : ℝ) (ht : 0 < t) :
      Ubar n (x, t) = U n (x, t) := by
    change P.piecewise (U n)
      (fun z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1)
        ((x, t) : ParabolicPoint) = U n (x, t)
    rw [Set.piecewise_eq_of_mem P (U n)
      (fun z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hDpos (n : ℕ) (x : Vec3) (t : ℝ) (ht : 0 < t)
      (i j : Fin 3) : Dbar n (x, t) i j = D n (x, t) i j := by
    change P.piecewise (D n) (fun _ => 0)
      ((x, t) : ParabolicPoint) i j = D n (x, t) i j
    rw [Set.piecewise_eq_of_mem P (D n) (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hEnergy (n : ℕ) :=
    lerayLimit_regularised_energy_bounds ρ a ha (εseq n) (hseq n).1
      (U n) (D n) (hData n).2.1 (hData n).2.2.1 (hData n).2.2.2
  have hInitial : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  let B : ℝ≥0∞ := A ^ (2 : ℕ)
  have hBtop : B < ⊤ := by
    dsimp [B, A]
    exact ENNReal.pow_lt_top hInitial.eLpNorm_lt_top
  have hUbarMeas (n : ℕ) : Measurable (Ubar n) := by
    have hUcont : ContinuousOn (U n) P := by
      apply continuousOn_pi.mpr
      intro i
      simpa [U, P] using (hData n).2.1 i
    have hIcont : Continuous
        (fun z : ParabolicPoint =>
          regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1) := by
      exact (regUniformMollifiedInitial_contDiff ρ (εseq n) (hseq n).1 ha).continuous.comp
        continuous_fst_parabolicPoint
    exact lerayLimit_measurableOn_extension P hPmeas (U n)
      (fun z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1)
      hUcont (hIcont.continuousOn.mono (Set.subset_univ (Pᶜ)))
  have hDbarMeas (n : ℕ) : Measurable (Dbar n) := by
    have hDcont : ContinuousOn (D n) P := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      simpa [D, U, P] using (hData n).2.2.1 i j
    exact lerayLimit_measurableOn_extension P hPmeas (D n)
      (fun _ => 0) hDcont continuousOn_const
  have hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => Ubar n (x, t) i) (fun x j => Dbar n (x, t) i j) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro i
    have hR := hregularised a ha (εseq n) (hseq n).1
    have hC1 := hR.2.2.2.2.2.2.2.1
    have hC1slice := lerayLimit_contDiff_spatial_slices
      (U n) P hC1 (by
        intro s hs x
        change x ∈ Set.univ ∧ 0 < s
        exact ⟨Set.mem_univ _, hs⟩)
    have hUeq : (fun x : Vec3 => Ubar n (x, t) i) =
        fun x => U n (x, t) i := by
      funext x
      exact congrArg (fun v : Vec3 => v i) (hUpos n x t ht)
    rw [hUeq]
    intro j
    have hbase := CKN.HasWeakGradientOn.of_contDiff
      (U := (Set.univ : Set Vec3))
      (f := fun x : Vec3 => U n (x, t) i) (hC1slice t ht i)
    have hsame : (fun x : Vec3 =>
        (fderiv ℝ (fun y : Vec3 => U n (y, t) i) x) (basisVec j)) =
        fun x => Dbar n (x, t) i j := by
      funext x
      rw [hDpos n x t ht i j]
      rfl
    simpa [hsame] using hbase j
  have hsliceBound (n : ℕ) (t : ℝ) (ht : 0 < t) :
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t)))
        2 volume ≤ A := by
    have hrawSlice : MemLp (fun x : Vec3 => U n (x, t)) 2 volume :=
      (hData n).1 t (le_of_lt ht)
    have hbarSlice : MemLp (fun x : Vec3 => Ubar n (x, t)) 2 volume := by
      apply (memLp_congr_ae (Filter.Eventually.of_forall fun x => hUpos n x t ht)).2
      exact hrawSlice
    have hcoord : MemLp
        (fun x : L2Vec3 => Ubar n (WithLp.ofLp x, t)) 2 volume :=
      hbarSlice.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    have hS : MemLp (regUniformVelocitySlice (Ubar n) t) 2 volume := by
      exact hcoord.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    have hchange := eLpNorm_comp_measurePreserving
      (p := (2 : ℝ≥0∞)) (f := (WithLp.toLp 2 : Vec3 → L2Vec3))
      hS.aestronglyMeasurable vec3ToL2Vec3_measurePreserving
    have hvector : eLpNorm
        (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume =
          eLpNorm (regUniformVelocitySlice (Ubar n) t) 2 volume := by
      have hfun : (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) =
          fun x => regUniformVelocitySlice (Ubar n) t (WithLp.toLp 2 x) := by
        funext x
        simp [regUniformVelocitySlice]
      rw [hfun]
      exact hchange
    rw [hvector]
    have hsq := (hEnergy n).1 t (le_of_lt ht)
    exact (ENNReal.pow_le_pow_left_iff
      (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hsliceIntegralBound (n : ℕ) (t : ℝ) (ht : 0 < t) :
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)
        ∂volume) ≤ B := by
    have hbarSlice : MemLp (fun x : Vec3 => Ubar n (x, t)) 2 volume :=
      (memLp_congr_ae (Filter.Eventually.of_forall fun x => hUpos n x t ht)).2
        ((hData n).1 t (le_of_lt ht))
    have hvectorMem : MemLp
        (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume :=
      hbarSlice.continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    have henergyIdentity := lerayLimit_eLpNorm_two_sq_eq_lintegral
      hvectorMem.aestronglyMeasurable
    have hpow : eLpNorm
        (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume ^ (2 : ℝ) ≤
          A ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow (hsliceBound n t ht) (by norm_num)
    have hIntBar : (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)
        ∂volume) ≤ B := by
      have hpoint (x : Vec3) :
          ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ) =
            ‖WithLp.toLp 2 (Ubar n (x, t))‖ₑ ^ (2 : ℝ) := by
        rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
      calc
        _ = ∫⁻ x : Vec3, ‖WithLp.toLp 2 (Ubar n (x, t))‖ₑ ^ (2 : ℝ)
              ∂volume := by
            exact lintegral_congr (fun x => hpoint x)
        _ = eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t)))
              2 volume ^ (2 : ℝ) := henergyIdentity.symm
        _ ≤ B := by
            dsimp [B]
            calc
              _ ≤ A ^ (2 : ℝ) := hpow
              _ = A ^ (2 : ℕ) := by norm_num [ENNReal.rpow_natCast]
    exact hIntBar
  have hbound : ∀ C : Set Vec3, IsCompact C →
      C ⊆ (Set.univ : Set Vec3) → ∀ b₁ b₂ : ℝ,
      Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t, t ∈ Icc b₁ b₂ →
        (∫⁻ x in C,
          ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)
          ∂volume) ≤ M := by
    intro C hC hCU b₁ b₂ hb
    refine ⟨B, hBtop, ?_⟩
    intro n t ht
    have hglobal := hsliceIntegralBound n t (hb ht)
    have hCmeasure : volume.restrict C ≤ volume := by
      simpa only [Measure.restrict_univ] using
        (Measure.restrict_mono_set volume hCU)
    have hrestrict := lintegral_mono' hCmeasure
      (le_rfl : (fun x : Vec3 => ENNReal.ofReal
        (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)) ≤ fun x =>
          ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ))
    simpa only [MeasureTheory.lintegral, Measure.restrict_apply_univ] using
      hrestrict.trans hglobal
  have hgradBound : ∀ C : Set Vec3, IsCompact C →
      C ⊆ (Set.univ : Set Vec3) → ∀ b₁ b₂ : ℝ,
      Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc b₁ b₂, ∫⁻ x in C,
          ENNReal.ofReal (spatialGradientSq (Ubar n) (Dbar n) (x, t))
          ∂volume) ≤ G := by
    intro C hC hCU b₁ b₂ hb
    refine ⟨B, hBtop, ?_⟩
    intro n
    have hInner (t : ℝ) (ht : t ∈ Icc b₁ b₂) :
        (∫⁻ x in C, ENNReal.ofReal
          (spatialGradientSq (Ubar n) (Dbar n) (x, t)) ∂volume) ≤
        ∫⁻ x : Vec3, ENNReal.ofReal
          (spatialGradientSq (Ubar n) (Dbar n) (x, t)) ∂volume := by
      have hCmeasure : volume.restrict C ≤ volume := by
        simpa only [Measure.restrict_univ] using
          (Measure.restrict_mono_set volume hCU)
      exact lintegral_mono' hCmeasure (le_rfl)
    have htimeMeasure : volume.restrict (Icc b₁ b₂) ≤ volume.restrict (Ioi 0) :=
      Measure.restrict_mono_set volume hb
    calc
      _ ≤ ∫⁻ t in Icc b₁ b₂, ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq (Ubar n) (Dbar n) (x, t)) ∂volume
          ∂volume := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            exact hInner t ht
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
          ENNReal.ofReal (spatialGradientSq (Ubar n) (Dbar n) (x, t)) ∂volume
          ∂volume := by
            exact lintegral_mono' htimeMeasure (le_rfl)
      _ ≤ B := (hEnergy n).2.2
  have hmod : ∀ C : Set Vec3, IsCompact C →
      C ⊆ (Set.univ : Set Vec3) → ∀ b₁ b₂ : ℝ,
      Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
      HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc b₁ b₂ → t ∈ Icc b₁ b₂ →
          |(∫ x : Vec3, ∑ i : Fin 3, Ubar n (x, t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, Ubar n (x, s) i * w x i ∂volume)| ≤
              A * dist t s + B * (dist t s) ^ θ := by
    intro C hC hCU b₁ b₂ hb w hw hwc hws
    obtain ⟨A, B, θ, hA, hB, hθ, hmod⟩ :=
      hregEquicontinuity a ha εseq hseq C hC hCU b₁ b₂ hb w hw hwc hws
    refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
    intro n s t hs ht
    have hpair (r : ℝ) (hr : 0 < r) :
        (∫ x : Vec3, ∑ i : Fin 3, Ubar n (x, r) i * w x i ∂volume) =
          ∫ x : Vec3, ∑ i : Fin 3, U n (x, r) i * w x i ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hUpos n x r hr]
    rw [hpair t (hb ht), hpair s (hb hs)]
    exact hmod n s t hs ht
  let : IsOpen (Set.univ : Set Vec3) := isOpen_univ
  let : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  let hbound' := compact_time_slice_bounds_of_interval_bounds
    ordConnected_Ioi Ubar hbound
  let hgradBound' := compact_time_gradient_bounds_of_interval_bounds
    ordConnected_Ioi Ubar Dbar hgradBound
  let hmod' := compact_time_pairing_modulus_of_interval_modulus
    ordConnected_Ioi Ubar hmod
  obtain ⟨K, χ, J, hK, hKcover, hχ, hJ, hJcover,
      hmem, σ, hσ, V, D, hweak, hVcont, huniform, hDweak⟩ :=
    exists_common_velocity_gradient_subsequence isOpen_univ isOpen_Ioi
      Ubar Dbar hUbarMeas hDbarMeas hbound' hgradBound' hmod'
  let v : Vec3 × ℝ → Vec3 := compactnessMollifiedLimit Ubar σ
  have hv : Measurable v :=
    measurable_compactnessMollifiedLimit Ubar σ hUbarMeas
  have hstrongRect := strong_l2_to_compactnessMollifiedLimit_on_exhaustion
    isOpen_univ isOpen_Ioi Ubar Dbar hUbarMeas hDbarMeas hweakGrad
    hbound' hgradBound' K χ J hK hKcover hχ
    (fun j => ⟨(hJ j).1, (hJ j).2.1⟩)
    hmem σ V hweak hVcont huniform
  obtain ⟨g, hg, hgEq, hgWeak⟩ :=
    compactness_gradient_limit_of_joint_limits isOpen_univ
      Ubar Dbar v σ K J hK hKcover hJ hJcover hweakGrad D hDweak
      hstrongRect
  refine ⟨σ, hσ, v, g, hv, hg, (by intro z; rfl), ?_, ?_, ?_, hgWeak,
    ?_, ?_⟩
  · intro t C hC hCU
    exact weak_slices_to_compactnessMollifiedLimit_on_compact isOpen_Ioi
      Ubar σ hUbarMeas K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx)
      hbound' hmem V hweak C hC hCU t
  · exact strong_l2_on_compacts_of_exhaustion K J
      (fun j => (hK j).2.2.1) (fun j => (hK j).2.2.2) hKcover
      (fun j => (hJ j).2.2.1) (fun j => (hJ j).2.2.2) hJcover
      (fun k z => (WithLp.toLp 2 (Ubar (σ k) z) : L2Vec3))
      (fun z => (WithLp.toLp 2 (v z) : L2Vec3))
      (fun j => (hstrongRect j).2)
  · intro Q hQ hQI
    exact weak_gradient_to_measurable_limit_on_compact
      Dbar σ K J hK hKcover hJ hJcover D hDweak
      g hgEq Q hQ hQI
  · intro C hC hCU a b habI M hM hMb
    exact compactness_limit_slice_bound isOpen_Ioi Ubar σ hUbarMeas
      K χ hK hKcover
      (fun j x hx => (hχ j).2.2.2.2 x hx)
      hbound' hmem V hweak C hC hCU (Icc a b) habI M hM hMb
  · intro C hC hCU a b habI G hG hGb
    exact compactness_limit_gradient_bound Ubar Dbar hDbarMeas σ
      K J hK hKcover hJ hJcover D hDweak g hg hgEq
      C hC hCU (Icc a b) isCompact_Icc habI G hG hGb


end CKN.Leray

end
