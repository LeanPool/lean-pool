/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessTimeGlue
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessBallPairing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls

/-!
# Compactness Slice

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Local slice energy bounds supply global `L²` fields after multiplication
by the cutoffs of a compact exhaustion. -/
theorem exists_cutoff_l2_fields_of_local_slice_bounds
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (u : ℕ → ParabolicPoint → Vec3) (huMeas : ∀ n, Measurable (u n))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ J →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M) :
    ∃ K : ℕ → Set Vec3, ∃ χ : ℕ → Vec3 → ℝ,
      (∀ j, IsCompact (K j) ∧ K j ⊆ U ∧ K j ⊆ K (j + 1) ∧
        K j ⊆ interior (K (j + 1))) ∧
      (⋃ j, K j = U) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧ HasCompactSupport (χ j) ∧
        tsupport (χ j) ⊆ U ∧ (∀ x, χ j x ∈ Icc (0 : ℝ) 1) ∧
        ∀ x ∈ K j, χ j x = 1) ∧
      ∀ n j (t : I), MemLp
        (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
        2 (volume : Measure Vec3) := by
  classical
  obtain ⟨K, χ, hK, hcover, hχ⟩ := exists_compact_exhaustion_cutoffs_vec3 U hU
  refine ⟨K, χ, hK, hcover, hχ, ?_⟩
  intro n j t
  let C : Set Vec3 := tsupport (χ j)
  have hC : IsCompact C := (hχ j).2.1
  have hCU : C ⊆ U := (hχ j).2.2.1
  obtain ⟨p, htp⟩ := exists_rational_compact_time_window_around hI t.property
  obtain ⟨M, hM, hBound⟩ :=
    hbound C hC hCU (Icc (p.1.1 : ℝ) p.1.2) isCompact_Icc p.property.2
  have hfinite :
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t.1))) ^
        (2 : ℝ) ∂volume) < ⊤ :=
    (hBound n t.1 ⟨htp.1.le, htp.2.le⟩).trans_lt hM
  have huSlice : Measurable (fun x : Vec3 => u n (x,t.1)) := by
    exact (huMeas n).comp (by fun_prop)
  let f : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (u n (x,t.1))
  have hf : MemLp f 2 (volume.restrict C) :=
    CKN.Foundation.memLp_two_vec3_of_lintegral_sq_lt_top
      (volume.restrict C) (fun x => u n (x,t.1)) huSlice hfinite
  have hχMeas : Measurable (χ j) := (hχ j).1.continuous.measurable
  have hχBound (x : Vec3) : |χ j x| ≤ 1 := by
    have hx := (hχ j).2.2.2.1 x
    rw [abs_of_nonneg hx.1]
    exact hx.2
  exact CKN.Foundation.memLp_two_cutoff_vec3_global hC.measurableSet f hf
    (χ j) hχMeas (Set.Subset.rfl) hχBound

/-- A compact-time slice energy bound controls the norms of the corresponding
global cutoff `L²` fields. -/
theorem cutoff_l2_norm_bound_on_time_window
    {J : Set ℝ} (u : ℕ → ParabolicPoint → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (χ : Vec3 → ℝ) (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hmem : ∀ n t, t ∈ J → MemLp
      (fun x => χ x • WithLp.toLp 2 (u n (x,t)))
      2 (volume : Measure Vec3))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hbound : ∀ n t, t ∈ J →
      (∫⁻ x in tsupport χ,
        ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^ (2 : ℝ)
        ∂volume) ≤ M) :
    ∀ n t, (ht : t ∈ J) →
      ‖(hmem n t ht).toLp
        (fun x => χ x • WithLp.toLp 2 (u n (x,t)))‖ ≤
      (M ^ (1 / 2 : ℝ)).toReal := by
  intro n t ht
  let C : Set Vec3 := tsupport χ
  have hfinite : (∫⁻ x in C,
      ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^ (2 : ℝ)
      ∂volume) < ⊤ := (hbound n t ht).trans_lt hM
  have huSlice : Measurable (fun x : Vec3 => u n (x,t)) :=
    (huMeas n).comp (by fun_prop)
  let f : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (u n (x,t))
  have hf : MemLp f 2 (volume.restrict C) :=
    CKN.Foundation.memLp_two_vec3_of_lintegral_sq_lt_top
      (volume.restrict C) (fun x => u n (x,t)) huSlice hfinite
  have hχMeas : Measurable χ := hχsmooth.continuous.measurable
  have hχBound (x : Vec3) : |χ x| ≤ 1 := by
    have hx := hχrange x
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have henergy : (∫⁻ x in C, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ≤ M := by
    simpa only [f, ← ofReal_norm, ← vec3EuclideanNorm_eq_l2] using
      hbound n t ht
  have hnorm' := CKN.Foundation.norm_toLp_two_cutoff_vec3_le
    hχcompact.measurableSet f hf χ hχMeas (Set.Subset.rfl)
    hχBound M hM henergy
  exact hnorm'

/-- The local slice bounds and smooth-test time modulus select one subsequence
whose cutoff slices converge weakly at every time. -/
theorem exists_common_subsequence_cutoff_weak_slices
    {U : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    (u : ℕ → ParabolicPoint → Vec3) (huMeas : ∀ n, Measurable (u n))
    (χ : ℕ → Vec3 → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧ HasCompactSupport (χ j) ∧
      tsupport (χ j) ⊆ U ∧ ∀ x, χ j x ∈ Icc (0 : ℝ) 1)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ J →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ J → t ∈ J →
          |(∫ x : Vec3, ∑ i : Fin 3, u n (x,t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, u n (x,s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3),
        (∀ j t x, Tendsto
          (fun k => inner ℝ ((hmem (σ k) j t).toLp
            (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
          (nhds (inner ℝ (V j t) x))) ∧
        (∀ j x, Continuous (fun t => inner ℝ (V j t) x)) ∧
        ∀ j (p : RationalCompactTimeWindow I) x ε, 0 < ε →
          ∀ᶠ k in atTop, ∀ t : RationalTimeSlice p,
            dist (inner ℝ ((hmem (σ k) j
              ⟨t.1, p.property.2 t.property⟩).toLp
              (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x)
              (inner ℝ (V j ⟨t.1, p.property.2 t.property⟩) x) < ε := by
  classical
  obtain ⟨ψ, hψreg, hψmem, hψdense⟩ :=
    exists_countable_dense_smooth_compact_vector_tests
  let E := Lp L2Vec3 2 (volume : Measure Vec3)
  let f : ℕ → ℕ → ℝ → E := fun n j t =>
    if ht : t ∈ I then
      (hmem n j ⟨t, ht⟩).toLp
        (fun y => χ j y • WithLp.toLp 2 (u n (y,t)))
    else 0
  let Cset : ℕ → Set Vec3 := fun j => tsupport (χ j)
  let M : ℕ → RationalCompactTimeWindow I → ℝ≥0∞ :=
    fun j p => Classical.choose (hbound (Cset j) (hχ j).2.1
      (hχ j).2.2.1 (Icc (p.1.1 : ℝ) p.1.2) isCompact_Icc p.property.2)
  have hM (j : ℕ) (p : RationalCompactTimeWindow I) :
      M j p < ⊤ ∧ ∀ n t, t ∈ Icc (p.1.1 : ℝ) p.1.2 →
        (∫⁻ x in Cset j,
          ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^ (2 : ℝ)
          ∂volume) ≤ M j p :=
    Classical.choose_spec (hbound (Cset j) (hχ j).2.1
      (hχ j).2.2.1 (Icc (p.1.1 : ℝ) p.1.2) isCompact_Icc p.property.2)
  let C : ℕ → RationalCompactTimeWindow I → ℝ :=
    fun j p => (M j p ^ (1 / 2 : ℝ)).toReal
  have hC (j : ℕ) (p : RationalCompactTimeWindow I) : 0 ≤ C j p :=
    ENNReal.toReal_nonneg
  have hnorm (n j : ℕ) (p : RationalCompactTimeWindow I) (t : ℝ)
      (ht : t ∈ Icc (p.1.1 : ℝ) p.1.2) : ‖f n j t‖ ≤ C j p := by
    have htI : t ∈ I := p.property.2 ht
    have hMeasSlice : Measurable (fun x : Vec3 => u n (x,t)) :=
      (huMeas n).comp (by fun_prop)
    let g : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (u n (x,t))
    have hfinite : (∫⁻ x in Cset j,
        ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^ (2 : ℝ)
        ∂volume) < ⊤ := ((hM j p).2 n t ht).trans_lt (hM j p).1
    have hg : MemLp g 2 (volume.restrict (Cset j)) :=
      CKN.Foundation.memLp_two_vec3_of_lintegral_sq_lt_top
        (volume.restrict (Cset j)) (fun x => u n (x,t)) hMeasSlice hfinite
    have hχMeas : Measurable (χ j) := (hχ j).1.continuous.measurable
    have hχBound (x : Vec3) : |χ j x| ≤ 1 := by
      have hx := (hχ j).2.2.2 x
      rw [abs_of_nonneg hx.1]
      exact hx.2
    have henergy : (∫⁻ x in Cset j, ‖g x‖ₑ ^ (2 : ℝ) ∂volume) ≤ M j p := by
      simpa only [g, ← ofReal_norm, ← vec3EuclideanNorm_eq_l2] using
        (hM j p).2 n t ht
    have hnorm' := CKN.Foundation.norm_toLp_two_cutoff_vec3_le
      (hχ j).2.1.measurableSet g hg (χ j) hχMeas (Set.Subset.rfl)
      hχBound (M j p) (hM j p).1 henergy
    simpa only [f, dite_eq_left htI, C, g] using hnorm'
  have hmod' (j : ℕ) (p : RationalCompactTimeWindow I) (m : ℕ) :
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n (s t : RationalTimeSlice p),
          |inner ℝ (f n j t.1) ((hψmem m).toLp (ψ m)) -
            inner ℝ (f n j s.1) ((hψmem m).toLp (ψ m))| ≤
              A * dist t s + B * (dist t s) ^ θ := by
    let w : Vec3 → L2Vec3 := fun y => χ j y • ψ m y
    have hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w :=
      (hχ j).1.smul (hψreg m).2
    have hwSupport : tsupport w ⊆ Cset j :=
      tsupport_smul_subset_left (χ j) (ψ m)
    have hwCompact : HasCompactSupport w :=
      (hχ j).2.1.of_isClosed_subset (isClosed_tsupport w) hwSupport
    obtain ⟨A, B, θ, hA, hB, hθ, hmodw⟩ :=
      hmod (Cset j) (hχ j).2.1 (hχ j).2.2.1
        (Icc (p.1.1 : ℝ) p.1.2) isCompact_Icc p.property.2 w
        hwSmooth hwCompact hwSupport
    refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
    intro n s t
    have hsI : s.1 ∈ I := p.property.2 s.property
    have htI : t.1 ∈ I := p.property.2 t.property
    have hpair (v : RationalTimeSlice p) (hvI : v.1 ∈ I) :
        inner ℝ (f n j v.1) ((hψmem m).toLp (ψ m)) =
          ∫ x : Vec3, ∑ i : Fin 3, u n (x,v.1) i * w x i ∂volume := by
      simpa only [f, dite_eq_left hvI, w] using
        inner_cutoff_vec3_eq_integral_dot (fun x => u n (x,v.1))
          (χ j) (ψ m) (hmem n j ⟨v.1, hvI⟩) (hψmem m)
    rw [hpair t htI, hpair s hsI]
    have hdist : dist t s = dist t.1 s.1 := rfl
    rw [hdist]
    exact hmodw n s.1 t.1 s.property t.property
  obtain ⟨σ, hσ, V, hweak, hcont, huniform⟩ :=
    exists_common_subsequence_all_time_weak_limit hI f
      (fun m => (hψmem m).toLp (ψ m)) hψdense C hC hnorm hmod'
  refine ⟨σ, hσ, V, ?_, hcont, ?_⟩
  · intro j t x
    have h := hweak j t x
    simpa only [f, dite_eq_left t.property] using h
  · intro j p x ε hε
    have h := huniform j p x ε hε
    filter_upwards [h] with k hk t
    have htI : t.1 ∈ I := p.property.2 t.property
    simpa only [f, dite_eq_left htI] using hk t

end CKN.Leray
