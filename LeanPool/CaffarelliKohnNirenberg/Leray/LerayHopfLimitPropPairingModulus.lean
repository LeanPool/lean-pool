/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropPairingBound
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropTransport
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierCoordinateL2Bridge
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# A uniform time modulus for regularized pairings

For a smooth, compactly supported, divergence-free test w, the pairing
`t ↦ ∫ u_ε(x,t) · w(x) dx` of a regularized solution of `thm:regularised` is
Lipschitz on `[0,∞)` with a constant depending only on w and on the energy
bound. This is the solenoidal case of `lem:reg-equicontinuity`: the pressure
term vanishes because w is divergence-free.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A field continuous on positive times is continuous on each positive time
slice. -/
theorem lerayHopfLimit_slice_continuous {F : ParabolicPoint → ℝ}
    (hF : ContinuousOn F (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    {t : ℝ} (ht : 0 < t) : Continuous (fun x : Vec3 => F (x, t)) := by
  have hemb : Continuous (fun x : Vec3 => (parabolicHomeomorph.symm (x, t) : ParabolicPoint)) :=
    parabolicHomeomorph.symm.continuous.comp (continuous_id.prodMk continuous_const)
  exact hF.comp_continuous hemb (fun x => ⟨mem_univ _, ht⟩)

/-- The Hilbert-space pairing of two coordinate `L²` fields is their
coordinate dot-product integral. -/
theorem lerayHopfLimit_inner_realVectorL2
    (a b : Vec3 → Vec3) (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    inner ℝ (realVectorL2OfCoordinateFunction a ha)
        (realVectorL2OfCoordinateFunction b hb) =
      ∫ x, ∑ i : Fin 3, a x i * b x i := by
  let F := realVectorL2OfCoordinateFunction a ha
  let G := realVectorL2OfCoordinateFunction b hb
  have hFrep := realVectorL2OfCoordinateFunction_rep a ha
  have hGrep := realVectorL2OfCoordinateFunction_rep b hb
  have htransport : MeasurePreserving
      (WithLp.toLp 2 : Vec3 → L2Vec3) volume volume := vec3ToL2Vec3_measurePreserving
  change inner ℝ F G = _
  rw [L2.inner_def]
  rw [← htransport.integral_comp (MeasurableEquiv.toLp 2 Vec3).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [hFrep, hGrep] with x hFx hGx
  have hFx' : ∀ i, (F (WithLp.toLp 2 x)) i = a x i := by
    intro i
    have := congrFun hFx i
    exact this
  have hGx' : ∀ i, (G (WithLp.toLp 2 x)) i = b x i := by
    intro i
    have := congrFun hGx i
    exact this
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hFx' i, hGx' i]
  simp [mul_comm]

/-- Joint continuous differentiability on positive times gives differentiability
along time and along space at every positive-time point. -/
theorem lerayHopfLimit_slice_differentiable (F : ParabolicPoint → ℝ)
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ContDiffOn ℝ 1 F (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (x : Vec3) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun s : ℝ => F (x, s)) t ∧
      DifferentiableAt ℝ (fun y : Vec3 => F (y, t)) x := by
  have h : ContDiffOn ℝ 1 (show Vec3 × ℝ → ℝ from F)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) := hC1
  have hopen : IsOpen ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) :=
    isOpen_univ.prod isOpen_Ioi
  have hmem : ((x, t) : Vec3 × ℝ) ∈ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) :=
    ⟨mem_univ _, ht⟩
  have hd : DifferentiableAt ℝ (show Vec3 × ℝ → ℝ from F) (x, t) :=
    (h.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by norm_num)
  constructor
  · exact hd.comp t ((differentiableAt_const x).prodMk differentiableAt_id)
  · exact hd.comp x (differentiableAt_id.prodMk (differentiableAt_const t))

/-- The time derivative of the pairing of a regularized velocity with a smooth
compactly supported test, at a positive time. -/
theorem lerayHopfLimit_regPairing_hasDerivAt
    (U : ParabolicPoint → Vec3) (w : Fin 3 → Vec3 → ℝ)
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) (hwc : ∀ i, HasCompactSupport (w i))
    (hUc : ∀ i, ContinuousOn (fun z => U z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtc : ∀ i, ContinuousOn (fun z => timePartial (fun y => U y i) z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => U z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtBound : ∀ δ T : ℝ, 0 < δ → δ < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
        ∀ i, |timePartial (fun y => U y i) z| ≤ C)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, ∑ i : Fin 3, U (x, s) i * w i x)
      (∫ x, ∑ i : Fin 3, timePartial (fun y => U y i) (x, t) * w i x) t := by
  obtain ⟨C, hC0, hC⟩ := hDtBound (t / 2) (t + 1) (by linarith only [ht])
    (by linarith only [ht])
  have hS : Ioo (t / 2) (t + 1) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith only [ht]) (by linarith only [ht])
  have hslice : ∀ s, 0 < s → ∀ i, Continuous (fun x : Vec3 => U (x, s) i) :=
    fun s hs i => lerayHopfLimit_slice_continuous (hUc i) hs
  have hDtslice : ∀ s, 0 < s → ∀ i,
      Continuous (fun x : Vec3 => timePartial (fun y => U y i) (x, s)) :=
    fun s hs i => lerayHopfLimit_slice_continuous (hDtc i) hs
  have hbint : Integrable (fun x => C * ∑ i : Fin 3, ‖w i x‖) :=
    (integrable_finsetSum _ (fun i _ =>
      (hw i).continuous.norm.integrable_of_hasCompactSupport (hwc i).norm)).const_mul C
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s x => ∑ i : Fin 3, U (x, s) i * w i x)
    (F' := fun s x => ∑ i : Fin 3, timePartial (fun y => U y i) (x, s) * w i x)
    (bound := fun x => C * ∑ i : Fin 3, ‖w i x‖) hS ?_ ?_ ?_ ?_ hbint ?_).2
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (continuous_finsetSum _ (fun i _ =>
      (hslice s hs i).mul (hw i).continuous)).aestronglyMeasurable
  · exact integrable_finsetSum _ (fun i _ =>
      lerayHopfLimit_integrable_mul_compact (hslice t ht i) (hw i).continuous (hwc i))
  · exact (continuous_finsetSum _ (fun i _ =>
      (hDtslice t ht i).mul (hw i).continuous)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x s hs => ?_)
    have hz : ((x, s) : ParabolicPoint) ∈
        spaceTimeSet (Set.univ : Set Vec3) (Icc (t / 2) (t + 1)) :=
      ⟨mem_univ _, le_of_lt hs.1, le_of_lt hs.2⟩
    rw [Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC _ hz i) (abs_nonneg _)
  · refine Filter.Eventually.of_forall (fun x s hs => ?_)
    have hspos : 0 < s := lt_trans (by linarith only [ht]) hs.1
    apply HasDerivAt.fun_sum
    intro i _
    have hd := (lerayHopfLimit_slice_differentiable (fun z => U z i) (hC1 i) x hspos).1
    exact hd.hasDerivAt.mul_const (w i x)

/-- The solenoidal pairing of a regularized solution is Lipschitz in time on
`[0,∞)`, with the constant of `lerayHopfLimit_pairing_rhs_bound`. -/
theorem lerayHopfLimit_regPairing_lipschitz
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (U : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceMem : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => U (x, t)) 2 volume)
    (hSliceCont : Continuous (fun t : Set.Ici (0 : ℝ) =>
      realVectorL2OfCoordinateFunction (fun x : Vec3 => U (x, t.1))
        (hSliceMem t.1 t.2)))
    (hSliceDiv : ∀ t : ℝ, 0 ≤ t → IsWeakDivFreeL2 (fun x => U (x, t)))
    (hUc : ∀ i, ContinuousOn (fun z => U z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDc : ∀ i j, ContinuousOn (fun z => spatialPartial (fun y => U y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDc : ∀ i j k, ContinuousOn (fun z =>
        spatialPartial (fun y => spatialPartial (fun x => U x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtc : ∀ i, ContinuousOn (fun z => timePartial (fun y => U y i) z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hpc : ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpc : ∀ i, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ i, ContDiffOn ℝ 1 (fun z => U z i)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => spatialPartial (fun y => U y i) j (x, z.2)) z.1)
    (hpdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (hDtBound : ∀ δ T : ℝ, 0 < δ → δ < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
        ∀ i, |timePartial (fun y => U y i) z| ≤ C)
    (hPDE : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => U y i) z -
        (∑ j : Fin 3, spatialPartial (fun y => spatialPartial (fun x => U x i) j y) j z) +
        (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε U z j *
          spatialPartial (fun y => U y i) j z) +
        spatialPartial (fun y => p y) i z = 0)
    (B : ℝ)
    (hB : ∀ t : ℝ, 0 ≤ t →
      (eLpNorm (regUniformVelocitySlice U t) 2 volume).toReal ≤ B)
    (w : Fin 3 → Vec3 → ℝ)
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) (hwc : ∀ i, HasCompactSupport (w i))
    (hdivw : ∀ x, ∑ i : Fin 3, spatialDeriv (w i) i x = 0)
    (K : ℝ)
    (hK : ∀ f J : Fin 3 → Vec3 → ℝ,
      (∀ i, MemLp (f i) 2 volume) → (∀ j, MemLp (J j) 2 volume) →
      (∀ i, ∫ x, f i x ^ 2 ≤ B ^ 2) → (∀ j, ∫ x, J j x ^ 2 ≤ B ^ 2) →
      |∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        (f i x * spatialDeriv (spatialDeriv (w i) j) j x +
          f i x * J j x * spatialDeriv (w i) j x)| ≤ K) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      |(∫ x, ∑ i : Fin 3, U (x, t) i * w i x) -
        ∫ x, ∑ i : Fin 3, U (x, s) i * w i x| ≤ K * |t - s| := by
  let g : ℝ → ℝ := fun s => ∫ x, ∑ i : Fin 3, U (x, s) i * w i x
  -- the slice bounds
  have hBnn : ∀ t : ℝ, 0 ≤ t → ∀ i, MemLp (fun x => U (x, t) i) 2 volume ∧
      ∫ x, U (x, t) i ^ 2 ≤ B ^ 2 := by
    intro t ht i
    have hg := lerayHopfLimit_toLp_memLp (hSliceMem t ht)
    obtain ⟨hmem, hle⟩ := lerayHopfLimit_integral_component_sq_le hg i
    refine ⟨hmem, hle.trans ?_⟩
    have hchange : eLpNorm (fun x : Vec3 => (WithLp.toLp 2 (U (x, t)) : L2Vec3)) 2 volume =
        eLpNorm (regUniformVelocitySlice U t) 2 volume := by
      have hS : MemLp (regUniformVelocitySlice U t) 2 volume := by
        have hcoord : MemLp (fun x : L2Vec3 => U (WithLp.ofLp x, t)) 2 volume :=
          (hSliceMem t ht).comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
        exact hcoord.continuousLinearMap_comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
      exact eLpNorm_comp_measurePreserving hS.aestronglyMeasurable
        vec3ToL2Vec3_measurePreserving
    rw [hchange]
    have h0 : 0 ≤ (eLpNorm (regUniformVelocitySlice U t) 2 volume).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h0 (hB t ht) 2
  have hJnn : ∀ t : ℝ, 0 ≤ t → ∀ j,
      MemLp (fun x => regUniformMollifiedVelocity ρ ε hε U (x, t) j) 2 volume ∧
      ∫ x, regUniformMollifiedVelocity ρ ε hε U (x, t) j ^ 2 ≤ B ^ 2 := by
    intro t ht j
    obtain ⟨hmem, hle⟩ := lerayHopfLimit_mollifiedInitial_component_sq_le ρ ε hε
      (hSliceMem t ht) j
    refine ⟨hmem, hle.trans ?_⟩
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hB t ht) 2
  -- derivative bound on positive times
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt g
      (∫ x, ∑ i : Fin 3, timePartial (fun y => U y i) (x, t) * w i x) t :=
    fun t ht => lerayHopfLimit_regPairing_hasDerivAt U w hw hwc hUc hDtc hC1 hDtBound ht
  have hderivBound : ∀ t : ℝ, 0 < t →
      ‖∫ x, ∑ i : Fin 3, timePartial (fun y => U y i) (x, t) * w i x‖ ≤ K := by
    intro t ht
    have hdiff := fun i x => lerayHopfLimit_slice_differentiable (fun z => U z i) (hC1 i) x ht
    have hidentity := lerayHopfLimit_pairing_equation_ibp
      (fun i x => U (x, t) i)
      (fun i j x => spatialPartial (fun y => U y i) j (x, t))
      (fun i j k x => spatialPartial (fun y => spatialPartial (fun x => U x i) j y) k (x, t))
      (fun x => p (x, t))
      (fun i x => spatialPartial (fun y => p y) i (x, t))
      (fun j x => regUniformMollifiedVelocity ρ ε hε U (x, t) j)
      (fun i x => timePartial (fun y => U y i) (x, t)) w
      (fun i => lerayHopfLimit_slice_continuous (hUc i) ht)
      (fun i x => (hdiff i x).2)
      (fun i j x => rfl)
      (fun i j => lerayHopfLimit_slice_continuous (hDc i j) ht)
      (fun i j x => hDdiff (x, t) ⟨mem_univ _, ht⟩ i j)
      (fun i j k x => rfl)
      (fun i j k => lerayHopfLimit_slice_continuous (hDDc i j k) ht)
      (lerayHopfLimit_slice_continuous hpc ht)
      (fun x => hpdiff (x, t) ⟨mem_univ _, ht⟩)
      (fun i x => rfl)
      (fun i => lerayHopfLimit_slice_continuous (hDpc i) ht)
      (fun j => (lerayHopfLimit_mollifiedInitial_contDiff ρ ε hε (hSliceMem t ht.le) j).of_le
        (by exact_mod_cast le_top))
      (lerayHopfLimit_mollifiedInitial_divergence_eq_zero ρ ε hε (hSliceDiv t ht.le))
      (fun i x => by
        have h := hPDE (x, t) ht i
        linarith only [h])
      hw hwc hdivw
    rw [hidentity, Real.norm_eq_abs]
    exact hK (fun i x => U (x, t) i)
      (fun j x => regUniformMollifiedVelocity ρ ε hε U (x, t) j)
      (fun i => (hBnn t ht.le i).1) (fun j => (hJnn t ht.le j).1)
      (fun i => (hBnn t ht.le i).2) (fun j => (hJnn t ht.le j).2)
  -- Lipschitz on positive times
  have hpos : ∀ s t : ℝ, 0 < s → 0 < t → |g t - g s| ≤ K * |t - s| := by
    intro s t hs ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := g) (s := Ioi (0 : ℝ))
      (fun x hx => (hderiv x hx).hasDerivWithinAt) (fun x hx => hderivBound x hx)
      (convex_Ioi 0) hs ht
    simpa only [Real.norm_eq_abs] using h
  -- continuity at zero from the right
  have hW : MemLp (fun x : Vec3 => fun i => w i x) 2 volume := by
    refine MemLp.of_eval (fun i => ?_)
    exact lerayHopfLimit_memLp_two_of_compact (hw i).continuous (hwc i)
  have hgrep : ∀ t : ℝ, (ht : 0 ≤ t) → g t = inner ℝ
      (realVectorL2OfCoordinateFunction (fun x : Vec3 => U (x, t)) (hSliceMem t ht))
      (realVectorL2OfCoordinateFunction (fun x : Vec3 => fun i => w i x) hW) := by
    intro t ht
    rw [lerayHopfLimit_inner_realVectorL2]
  have hgcont : ContinuousWithinAt g (Ici 0) 0 := by
    have hc : Continuous (fun t : Set.Ici (0 : ℝ) => g t.1) := by
      have heq : (fun t : Set.Ici (0 : ℝ) => g t.1) = fun t => inner ℝ
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => U (x, t.1))
            (hSliceMem t.1 t.2))
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => fun i => w i x) hW) := by
        funext t
        exact hgrep t.1 t.2
      rw [heq]
      exact hSliceCont.inner continuous_const
    have hcon : ContinuousOn g (Ici 0) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hc
    exact hcon 0 self_mem_Ici
  have hzero : ∀ t : ℝ, 0 < t → |g t - g 0| ≤ K * |t - 0| := by
    intro t ht
    have hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      (hgcont.mono Ioi_subset_Ici_self).tendsto
    have hleft : Tendsto (fun s => |g t - g s|) (𝓝[>] (0 : ℝ)) (𝓝 (|g t - g 0|)) :=
      (tendsto_const_nhds.sub hlim).abs
    have hright : Tendsto (fun s : ℝ => K * |t - s|) (𝓝[>] (0 : ℝ)) (𝓝 (K * |t - 0|)) := by
      have hc : Continuous (fun s : ℝ => K * |t - s|) := by fun_prop
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hleft hright ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hpos s t hs ht
  intro s t hs ht
  change |g t - g s| ≤ K * |t - s|
  rcases hs.lt_or_eq with hs' | hs'
  · rcases ht.lt_or_eq with ht' | ht'
    · exact hpos s t hs' ht'
    · subst ht'
      have h := hzero s hs'
      rw [abs_sub_comm, abs_sub_comm 0 s]
      simpa only [sub_zero] using h
  · subst hs'
    rcases ht.lt_or_eq with ht' | ht'
    · exact hzero t ht'
    · subst ht'
      simp

end CKN.Leray

end
