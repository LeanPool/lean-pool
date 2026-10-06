/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingFourierField
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocity
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityReg
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselGlobalPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalBounds

/-!
# Higher Bessel lifts of the regularized velocity

Every even-order Bessel lift gives a continuous frequency trajectory.
Its inverse Bessel weight represents the Fourier transform of the
same physical regularized velocity.
-/

public section

open MeasureTheory FourierTransform Complex Set
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN.Leray
open CKN CKN.Foundation.Parabolic

/-- Frequency trajectory of a Bessel lift of order `2(n+2)`, extended
from a finite interval by clamping time. -/
@[expose] def lpsRegR12HighLiftFreq (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (t : ℝ) : ComplexVectorL2 :=
  Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
    ((v (CKN.Leray.regularizedMildTimeClamp T hT t)).toLp)

/-- A higher Bessel lift has a continuous weighted Fourier
trajectory (`prop:lps-smoothing`). -/
theorem lps_regR12HighLiftFreq_continuous (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2)) :
    Continuous (lpsRegR12HighLiftFreq n T hT v) := by
  unfold lpsRegR12HighLiftFreq
  have h := (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).continuous.comp
    ((BesselPotentialSpace.toLpₗᵢ L2Vec3 ComplexVec3 _ 2).continuous.comp
      (v.continuous.comp
        (CKN.Leray.regularizedMildTimeClamp_continuous T hT)))
  simpa only [Function.comp_def, BesselPotentialSpace.toLpₗᵢ_apply] using h

/-- The weighted frequency trajectory has norm bounded by its
Bessel lift on every time slice. -/
theorem lps_regR12HighLiftFreq_norm_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2)) (t : ℝ) :
    ‖lpsRegR12HighLiftFreq n T hT v t‖ ≤ ‖v‖ := by
  unfold lpsRegR12HighLiftFreq
  rw [LinearIsometryEquiv.norm_map, BesselPotentialSpace.norm_toLp_eq]
  exact v.norm_coe_le_norm _

/-- The physical regularized curve has the inverse Bessel-weight
Fourier representation of every higher lift on its time interval
(`prop:lps-smoothing`). -/
theorem lps_regR12HighLiftFreq_curve_ae_eq
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ((CKN.Leray.regR12FreqCurve ρ ε hε a ha t : ComplexVectorL2) :
      L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => ((((1 + ‖ξ‖ ^ 2) ^
        (-((2 * (n + 2) : ℕ) : ℝ) / 2) : ℝ) : ℝ) : ℂ) •
          ((lpsRegR12HighLiftFreq n T hT v t : ComplexVectorL2) :
            L2Vec3 → ComplexVec3) ξ := by
  have hclamp : CKN.Leray.regularizedMildTimeClamp T hT t = ⟨t, ht⟩ :=
    CKN.Leray.regularizedMildTimeClamp_eq_of_mem T hT ht
  have h := CKN.Leray.regularisedBesselSobolevToL2_fourier_ae
    ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v ⟨t, ht⟩)
  have hvt := hv ⟨t, ht⟩
  rw [CKN.Leray.regularisedBesselSobolevToL2CLM_apply] at hvt
  rw [hvt] at h
  unfold CKN.Leray.regR12FreqCurve lpsRegR12HighLiftFreq
  rw [hclamp]
  exact h

/-- The inverse order-four weight and the extra Bessel damping combine
to the inverse weight of order `2(n+2)` (`prop:lps-smoothing`). -/
theorem lps_damped_base_weight_eq (n : ℕ) (ξ : L2Vec3) :
    (((1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ) *
      (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) =
    (((1 + ‖ξ‖ ^ 2) ^
      (-((2 * (n + 2) : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  have hb : 0 < (1 + ‖ξ‖ ^ 2 : ℝ) := by positivity
  rw [← Complex.ofReal_mul, ← Real.rpow_add hb]
  congr 1
  push_cast
  ring_nf

/-- On a finite interval, the physical regularized velocity is the
high-Bessel inverse Fourier field with the excess weight moved into
the multiplier (`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_eq_high_model
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (z : ParabolicPoint) (hz : z.2 ∈ Icc 0 T) (i : Fin 3) :
    CKN.Leray.regR12Velocity ρ ε hε a ha z i =
      CKN.Leray.regR12SpaceTimeField (CKN.Leray.regR12CoordCLM i)
        (lpsDampedFourierWordSymbol n [])
        (lpsRegR12HighLiftFreq n T hT v) z := by
  have hfreq := lps_regR12HighLiftFreq_curve_ae_eq
    ρ ε hε a ha n T hT v hv z.2 hz
  have hae :
      ((CKN.Leray.regR12FreqCurve ρ ε hε a ha z.2 : ComplexVectorL2) :
        L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => lpsDampedFourierWordSymbol n [] ξ •
        (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          ((lpsRegR12HighLiftFreq n T hT v z.2 : ComplexVectorL2) :
            L2Vec3 → ComplexVec3) ξ := by
    refine hfreq.trans (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [lpsDampedFourierWordSymbol,
      lpsFourierWordSymbol, List.map_nil, List.prod_nil, one_mul,
      smul_smul]
    rw [lps_damped_base_weight_eq]
  unfold CKN.Leray.regR12Velocity CKN.Leray.regR12SpaceTimeField
    CKN.Leray.regR12WeightedField
  rw [Real.fourierInv_congr_ae hae]

/-- Every classical ordered derivative of the physical regularized
velocity on a finite interval is the corresponding high-Bessel inverse
Fourier field (`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_wordDeriv_eq_high_model
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3)
    (α : List (Fin 3)) (hα : α.length ≤ 2 * (n + 1)) :
    wordDeriv α (fun x : Vec3 =>
      CKN.Leray.regR12Velocity ρ ε hε a ha (x, t) i) =
      fun x : Vec3 => CKN.Leray.regR12SpaceTimeField
        (CKN.Leray.regR12CoordCLM i)
        (lpsDampedFourierWordSymbol n α)
        (lpsRegR12HighLiftFreq n T hT v) (x, t) := by
  have hbase : (fun x : Vec3 =>
      CKN.Leray.regR12Velocity ρ ε hε a ha (x, t) i) =
      fun x : Vec3 => CKN.Leray.regR12SpaceTimeField
        (CKN.Leray.regR12CoordCLM i)
        (lpsDampedFourierWordSymbol n [])
        (lpsRegR12HighLiftFreq n T hT v) (x, t) := by
    funext x
    exact lps_regR12Velocity_eq_high_model
      ρ ε hε a ha n T hT v hv (x, t) ht i
  rw [hbase]
  exact lps_dampedSpaceTimeField_wordDeriv n α hα
    (CKN.Leray.regR12CoordCLM i)
    (lpsRegR12HighLiftFreq n T hT v) t

/-- Ordered physical spatial derivatives of the regularized velocity
belong to space-time `L²` on every positive-time slab through the
available higher Bessel order (`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_wordDeriv_memLp_slab
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (δ T : ℝ) (hδ : 0 ≤ δ) (hδT : δ < T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (i : Fin 3) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1)) :
    MemLp (fun z : ParabolicPoint =>
      wordDeriv α (fun x : Vec3 =>
        CKN.Leray.regR12Velocity ρ ε hε a ha (x, z.2) i) z.1)
      2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  have hT : 0 ≤ T := le_of_lt (lt_of_le_of_lt hδ hδT)
  have hslab : MeasurableSet
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hin : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T),
      z.2 ∈ Icc 0 T :=
    fun z hz => ⟨hδ.trans hz.2.1.le, hz.2.2.le⟩
  have hGB : ∀ t ∈ Ioo δ T,
      ‖lpsRegR12HighLiftFreq n T hT v t‖ ≤ ‖v‖ :=
    fun t _ => lps_regR12HighLiftFreq_norm_le n T hT v t
  refine (memLp_congr_ae ?_).2
    (CKN.Leray.regR12SpaceTimeField_memLp_slab
      (CKN.Leray.regR12CoordCLM i)
      (lpsDampedFourierWordSymbol n α)
      (lps_dampedFourierWordSymbol_continuous n α).aestronglyMeasurable
      ((2 * π) ^ α.length) (by positivity)
      (lps_dampedFourierWordSymbol_norm_le n α hα)
      (lpsRegR12HighLiftFreq n T hT v)
      (lps_regR12HighLiftFreq_continuous n T hT v)
      δ T ‖v‖ hGB)
  filter_upwards [ae_restrict_mem hslab] with z hz
  exact congrFun (lps_regR12Velocity_wordDeriv_eq_high_model
    ρ ε hε a ha n T hT v hv z.2 (hin z hz) i α hα) z.1

/-- A higher Bessel lift makes every ordered physical derivative
square-integrable on each closed-interval slice
(`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_wordDeriv_memLp_slice_of_lift
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (v : C(CKN.Leray.RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3
        ((2 * (n + 2) : ℕ) : ℝ) 2))
    (hv : ∀ t : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v t) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3)
    (α : List (Fin 3)) (hα : α.length ≤ 2 * (n + 1)) :
    MemLp (wordDeriv α (fun x : Vec3 =>
      CKN.Leray.regR12Velocity ρ ε hε a ha (x, t) i)) 2 volume := by
  rw [lps_regR12Velocity_wordDeriv_eq_high_model
    ρ ε hε a ha n T hT v hv t ht i α hα]
  exact lps_dampedSpaceTimeField_slice_memLp n α hα
    (CKN.Leray.regR12CoordCLM i)
    (lpsRegR12HighLiftFreq n T hT v t)

/-- Every nonnegative-time slice of the actual regularized velocity
has square-integrable classical derivatives at every ordered spatial
word (`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_all_word_memLp_slice
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 3)
    (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x : Vec3 =>
      CKN.Leray.regR12Velocity ρ ε hε a ha (x, t) i)) 2 volume := by
  let n : ℕ := α.length
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (n + 2) t ht
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval t,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  exact lps_regR12Velocity_wordDeriv_memLp_slice_of_lift
    ρ ε hε a ha n t ht v hv' t ⟨ht, le_rfl⟩ i α (by dsimp [n]; omega)

/-- Every ordered spatial derivative of the physical regularized
velocity is jointly continuous at positive times
(`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_all_word_continuousOn
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (i : Fin 3) (α : List (Fin 3)) :
    ContinuousOn (fun z : ParabolicPoint =>
      wordDeriv α (fun x : Vec3 =>
        CKN.Leray.regR12Velocity ρ ε hε a ha (x, z.2) i) z.1)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
  let n : ℕ := α.length
  have hα : α.length ≤ 2 * (n + 1) := by dsimp [n]; omega
  refine CKN.Leray.regR12_continuousOn_of_local_models fun T hT => ?_
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (n + 2) T hT.le
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  refine ⟨fun z : Vec3 × ℝ =>
      CKN.Leray.regR12SpaceTimeField (CKN.Leray.regR12CoordCLM i)
        (lpsDampedFourierWordSymbol n α)
        (lpsRegR12HighLiftFreq n T hT.le v) (z.1, z.2),
    lps_dampedSpaceTimeField_continuous n α hα
      (CKN.Leray.regR12CoordCLM i)
      (lpsRegR12HighLiftFreq n T hT.le v)
      (lps_regR12HighLiftFreq_continuous n T hT.le v), ?_⟩
  intro z hz
  exact congrFun (lps_regR12Velocity_wordDeriv_eq_high_model
    ρ ε hε a ha n T hT.le v hv' z.2
    ⟨hz.1.le, hz.2.le⟩ i α hα) z.1

end ESS
