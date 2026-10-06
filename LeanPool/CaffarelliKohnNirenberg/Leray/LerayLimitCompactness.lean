/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitConditions
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

private theorem lerayLimit_piecewise_agrees_on_source
    {α β : Type*} (P : Set α) (f g : α → β) {z : α} (hz : z ∈ P) :
    lerayLimitPiecewise P f g z = f z := by
  classical
  simpa [lerayLimitPiecewise] using Set.piecewise_eq_of_mem P f g hz

private theorem lerayLimit_velocity_positive_time_identity
    (P : Set ParabolicPoint) (U : ℕ → ParabolicPoint → Vec3)
    (initial : ℕ → ParabolicPoint → Vec3)
    (hPositive : ∀ x t, 0 < t → (x, t) ∈ P) :
    ∀ n x t, 0 < t →
      lerayLimitPiecewise P (U n) (initial n) (x, t) = U n (x, t) := by
  intro n x t ht
  exact lerayLimit_piecewise_agrees_on_source P (U n) (initial n) (hPositive x t ht)

private theorem lerayLimit_gradient_positive_time_identity
    (P : Set ParabolicPoint) (D : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (hPositive : ∀ x t, 0 < t → (x, t) ∈ P) :
    ∀ n x t, 0 < t → ∀ i j,
      lerayLimitPiecewise P (D n) (fun _ => 0) (x, t) i j = D n (x, t) i j := by
  intro n x t ht
  have heq := lerayLimit_piecewise_agrees_on_source P (D n) (fun _ => 0)
    (hPositive x t ht)
  exact fun i j => congrArg (fun F => F i j) heq

private theorem lerayLimit_piecewise_velocity_measurable
    (P : Set ParabolicPoint) [∀ x : ParabolicPoint, Decidable (x ∈ P)]
    (hP : MeasurableSet P)
    (U : ℕ → ParabolicPoint → Vec3) (initial : ℕ → ParabolicPoint → Vec3)
    (hU : ∀ n, ContinuousOn (U n) P) (hinitial : ∀ n, Continuous (initial n)) :
    ∀ n, Measurable (P.piecewise (U n) (initial n)) := by
  classical
  intro n
  have hInitialOn : ContinuousOn (initial n) Pᶜ :=
    (hinitial n).continuousOn.mono (Set.subset_univ (Pᶜ))
  exact lerayLimit_measurableOn_extension P hP (U n) (initial n) (hU n) hInitialOn

private theorem lerayLimit_piecewise_gradient_measurable
    (P : Set ParabolicPoint) [∀ x : ParabolicPoint, Decidable (x ∈ P)]
    (hP : MeasurableSet P)
    (D : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (hD : ∀ n, ContinuousOn (D n) P) :
    ∀ n, Measurable (P.piecewise (D n) (fun _ => 0)) := by
  classical
  intro n
  exact lerayLimit_measurableOn_extension P hP (D n) (fun _ => 0) (hD n)
    continuousOn_const

private theorem lerayLimit_piecewise_velocity_hasWeakGradient
    (P : Set ParabolicPoint) (U : ℕ → ParabolicPoint → Vec3)
    (Ubar : ℕ → ParabolicPoint → Vec3)
    (Dbar : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (hC1 : (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ n i, ContDiffOn ℝ 1 (fun z : ParabolicPoint => U n z i) P))
    (hPpositive : ∀ t : ℝ, 0 < t → ∀ x : Vec3, (x, t) ∈ P)
    (hUpos : ∀ n x t, 0 < t → Ubar n (x, t) = U n (x, t))
    (hDpos : ∀ n x t, 0 < t → ∀ i j,
      Dbar n (x, t) i j = spatialPartial (fun y => U n y i) j (x, t)) :
    ∀ n, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => Ubar n (x, t) i) (fun x j => Dbar n (x, t) i j) := by
  intro n
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  intro i
  let : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
  let : NormedAddCommGroup ParabolicPoint := inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
  let : NormedSpace ℝ ParabolicPoint := inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
  have hC1slice := lerayLimit_contDiff_spatial_slices (U n) P (by
    intro i
    exact hC1 n i) (by
    exact hPpositive)
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

private theorem lerayLimit_piecewise_vector_slice_bound
    (U Ubar : ℕ → ParabolicPoint → Vec3) (A : ℝ≥0∞)
    (hUpos : ∀ n x t, 0 < t → Ubar n (x, t) = U n (x, t))
    (hSliceMem : ∀ n t, 0 ≤ t → MemLp (fun x => U n (x, t)) 2 volume)
    (hEnergy : ∀ n t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (Ubar n) t) 2 volume ^ (2 : ℕ) ≤ A ^ (2 : ℕ)) :
    ∀ n t, 0 < t →
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume ≤ A := by
  intro n t ht
  have hbarSlice : MemLp (fun x : Vec3 => Ubar n (x, t)) 2 volume := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun x => hUpos n x t ht)).2
    exact hSliceMem n t (le_of_lt ht)
  have hcoord : MemLp
      (fun x : L2Vec3 => Ubar n (WithLp.ofLp x, t)) 2 volume :=
    hbarSlice.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  have hS : MemLp (regUniformVelocitySlice (Ubar n) t) 2 volume :=
    hcoord.continuousLinearMap_comp
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
  have hsq := hEnergy n t (le_of_lt ht)
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

private theorem lerayLimit_piecewise_slice_lintegral_bound
    (U Ubar : ℕ → ParabolicPoint → Vec3) (A B : ℝ≥0∞)
    (hAB : A ^ (2 : ℕ) = B)
    (hUpos : ∀ n x t, 0 < t → Ubar n (x, t) = U n (x, t))
    (hSliceMem : ∀ n t, 0 ≤ t → MemLp (fun x => U n (x, t)) 2 volume)
    (hVectorBound : ∀ n t, 0 < t →
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume ≤ A) :
    ∀ n t, 0 < t →
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)
        ∂volume) ≤ B := by
  intro n t ht
  have hbarSlice : MemLp (fun x : Vec3 => Ubar n (x, t)) 2 volume :=
    (memLp_congr_ae (Filter.Eventually.of_forall fun x => hUpos n x t ht)).2
      (hSliceMem n t (le_of_lt ht))
  have hvectorMem : MemLp
      (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume :=
    hbarSlice.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have henergyIdentity := lerayLimit_eLpNorm_two_sq_eq_lintegral
    hvectorMem.aestronglyMeasurable
  have hpow : eLpNorm
      (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume ^ (2 : ℝ) ≤
        A ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow (hVectorBound n t ht) (by norm_num)
  have hpoint (x : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ) =
        ‖WithLp.toLp 2 (Ubar n (x, t))‖ₑ ^ (2 : ℝ) := by
    rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
  calc
    _ = ∫⁻ x : Vec3, ‖WithLp.toLp 2 (Ubar n (x, t))‖ₑ ^ (2 : ℝ) ∂volume :=
      lintegral_congr (fun x => hpoint x)
    _ = eLpNorm (fun x : Vec3 => WithLp.toLp 2 (Ubar n (x, t))) 2 volume ^ (2 : ℝ) :=
      henergyIdentity.symm
    _ ≤ B := by
      calc
        _ ≤ A ^ (2 : ℝ) := hpow
        _ = B := by
          rw [← hAB]
          norm_num [ENNReal.rpow_natCast]

private theorem lerayLimit_piecewise_compact_slice_bound
    (Ubar : ℕ → ParabolicPoint → Vec3) (B : ℝ≥0∞) (hBtop : B < ⊤)
    (hSliceBound : ∀ n t, 0 < t →
      (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)
        ∂volume) ≤ B) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t, t ∈ Icc b₁ b₂ →
        (∫⁻ x in C, ENNReal.ofReal
          (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ) ∂volume) ≤ M := by
  intro C _hC hCU b₁ b₂ hb
  refine ⟨B, hBtop, ?_⟩
  intro n t ht
  have hglobal := hSliceBound n t (hb ht)
  have hCmeasure : volume.restrict C ≤ volume := by
    simpa only [Measure.restrict_univ] using Measure.restrict_mono_set volume hCU
  have hrestrict := lintegral_mono' hCmeasure
    (le_rfl : (fun x : Vec3 => ENNReal.ofReal
      (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ)) ≤ fun x =>
        ENNReal.ofReal (vec3EuclideanNorm (Ubar n (x, t))) ^ (2 : ℝ))
  simpa only [MeasureTheory.lintegral, Measure.restrict_apply_univ] using
    hrestrict.trans hglobal

private theorem lerayLimit_piecewise_compact_gradient_bound
    (Ubar : ℕ → ParabolicPoint → Vec3)
    (gradient : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (B : ℝ≥0∞) (hBtop : B < ⊤)
    (hDissipation : ∀ n,
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq (Ubar n) (gradient n) (x, t))
        ∂volume ∂volume) ≤ B) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc b₁ b₂, ∫⁻ x in C,
          ENNReal.ofReal (spatialGradientSq (Ubar n) (gradient n) (x, t))
          ∂volume) ≤ G := by
  intro C _hC hCU b₁ b₂ hb
  refine ⟨B, hBtop, ?_⟩
  intro n
  have hInner (t : ℝ) (ht : t ∈ Icc b₁ b₂) :
      (∫⁻ x in C, ENNReal.ofReal
        (spatialGradientSq (Ubar n) (gradient n) (x, t)) ∂volume) ≤
      ∫⁻ x : Vec3, ENNReal.ofReal
        (spatialGradientSq (Ubar n) (gradient n) (x, t)) ∂volume := by
    have hCmeasure : volume.restrict C ≤ volume := by
      simpa only [Measure.restrict_univ] using Measure.restrict_mono_set volume hCU
    exact lintegral_mono' hCmeasure (le_rfl)
  have htimeMeasure : volume.restrict (Icc b₁ b₂) ≤ volume.restrict (Ioi 0) :=
    Measure.restrict_mono_set volume hb
  calc
    _ ≤ ∫⁻ t in Icc b₁ b₂, ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq (Ubar n) (gradient n) (x, t)) ∂volume
        ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hInner t ht
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq (Ubar n) (gradient n) (x, t)) ∂volume
        ∂volume := lintegral_mono' htimeMeasure (le_rfl)
    _ ≤ B := hDissipation n

private theorem lerayLimit_piecewise_pairing_modulus
    (U Ubar : ℕ → ParabolicPoint → Vec3)
    (hUpos : ∀ n x t, 0 < t → Ubar n (x, t) = U n (x, t))
    (hregularity : ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc b₁ b₂ → t ∈ Icc b₁ b₂ →
          |(∫ x : Vec3, ∑ i : Fin 3, U n (x, t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, U n (x, s) i * w x i ∂volume)| ≤
              A * dist t s + B * (dist t s) ^ θ) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc b₁ b₂ → t ∈ Icc b₁ b₂ →
          |(∫ x : Vec3, ∑ i : Fin 3, Ubar n (x, t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, Ubar n (x, s) i * w x i ∂volume)| ≤
              A * dist t s + B * (dist t s) ^ θ := by
  intro C hC hCU b₁ b₂ hb w hw hwc hws
  obtain ⟨A, B, θ, hA, hB, hθ, hmod⟩ := hregularity C hC hCU b₁ b₂ hb
    w hw hwc hws
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

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)

/-- Local compactness and slice energy bounds for regularized solutions. -/
theorem lerayLimit_local_compactness
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε), CKN.lerayAssemblyRegularisedConditions ρ uε pε a ha ε hε)
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
  have hPositive (x : Vec3) (t : ℝ) (ht : 0 < t) : (x, t) ∈ P := by
    change x ∈ Set.univ ∧ 0 < t
    exact ⟨Set.mem_univ _, ht⟩
  have hUpos : ∀ n x t, 0 < t → Ubar n (x, t) = U n (x, t) := by
    simpa [Ubar] using
      lerayLimit_velocity_positive_time_identity P U
        (fun n z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1)
        hPositive
  have hDpos : ∀ n x t, 0 < t → ∀ i j, Dbar n (x, t) i j = D n (x, t) i j := by
    simpa [Dbar] using lerayLimit_gradient_positive_time_identity P D hPositive
  have hEnergy (n : ℕ) :=
    lerayLimit_regularised_energy_bounds ρ a ha (εseq n) (hseq n).1
      (U n) (D n) (hData n).2.1 (hData n).2.2.1 (hData n).2.2.2
  have hInitial : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  let B : ℝ≥0∞ := A ^ (2 : ℕ)
  have hBtop : B < ⊤ := ENNReal.pow_lt_top hInitial.eLpNorm_lt_top
  have hUbarMeas : ∀ n, Measurable (Ubar n) := by
    intro n
    simpa [Ubar, lerayLimitPiecewise] using
      (lerayLimit_piecewise_velocity_measurable P hPmeas U
        (fun n z => regUniformMollifiedInitial ρ (εseq n) (hseq n).1 a z.1)
        (by intro n; apply continuousOn_pi.mpr; intro i; simpa [U, P] using (hData n).2.1 i)
        (by
          intro n
          exact (regUniformMollifiedInitial_contDiff ρ (εseq n) (hseq n).1 ha).continuous.comp
            continuous_fst_parabolicPoint) n)
  have hDbarMeas : ∀ n, Measurable (Dbar n) := by
    intro n
    simpa [Dbar, lerayLimitPiecewise] using
      (lerayLimit_piecewise_gradient_measurable P hPmeas D (by
        intro n
        apply continuousOn_pi.mpr
        intro i
        apply continuousOn_pi.mpr
        intro j
        simpa [D, U, P] using (hData n).2.2.1 i j) n)
  have hweakGrad := lerayLimit_piecewise_velocity_hasWeakGradient P U Ubar Dbar
    (by intro n i; exact (hregularised a ha (εseq n) (hseq n).1).2.2.2.2.2.2.2.1 i)
    (by intro t ht x; exact hPositive x t ht)
    (by intro n x t ht; exact hUpos n x t ht)
    (by intro n x t ht i j; simpa [D] using hDpos n x t ht i j)
  have hsliceBound := lerayLimit_piecewise_vector_slice_bound U Ubar A
    (by intro n x t ht; exact hUpos n x t ht)
    (by intro n t ht; exact (hData n).1 t ht)
    (by intro n t ht; exact (hEnergy n).1 t ht)
  have hsliceIntegralBound := lerayLimit_piecewise_slice_lintegral_bound U Ubar A B (by rfl)
    (by intro n x t ht; exact hUpos n x t ht)
    (by intro n t ht; exact (hData n).1 t ht)
    hsliceBound
  have hbound := lerayLimit_piecewise_compact_slice_bound Ubar B hBtop hsliceIntegralBound
  have hgradBound := lerayLimit_piecewise_compact_gradient_bound Ubar Dbar B hBtop
    (by intro n; exact (hEnergy n).2.2)
  have hmod := lerayLimit_piecewise_pairing_modulus U Ubar
    (by intro n x t ht; exact hUpos n x t ht)
    (hregEquicontinuity a ha εseq hseq)
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
