/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevLeibniz
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1SliceBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compactly supported smooth approximation for whole-space Sobolev families

Finite families of whole-space Sobolev functions admit smooth compactly
supported approximations in every derivative represented by the family.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped Convolution Topology ENNReal

noncomputable section

namespace CKN

private theorem localSobolevMollify_spatialDeriv_scale {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a c : ℝ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => a * h (c • y)) i x =
      a * (c * spatialDeriv h i (c • x)) := by
  have h1 : HasFDerivAt (fun y : Vec3 => c • y)
      (c • ContinuousLinearMap.id ℝ Vec3) x :=
    (hasFDerivAt_id x).const_smul c
  have h2 : HasFDerivAt (fun y => a * h (c • y))
      (a • (fderiv ℝ h (c • x)).comp (c • ContinuousLinearMap.id ℝ Vec3)) x :=
    ((hh.differentiable (by simp) (c • x)).hasFDerivAt.comp x h1).const_mul a
  unfold spatialDeriv
  rw [h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

private theorem localSobolevMollify_wordDeriv_scale {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a c : ℝ) (α : List (Fin 3)) :
    wordDeriv α (fun x => a * h (c • x)) =
      fun x => a * c ^ α.length * wordDeriv α h (c • x) := by
  induction α generalizing h a with
  | nil => simp [wordDeriv]
  | cons i α ih =>
      have hsp := localSobolevMollify_spatialDeriv_scale hh a c i
      have hderiv : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv h i) :=
        contDiff_wordDeriv hh [i]
      have hnext := ih hderiv (a * c)
      ext x
      change wordDeriv α (spatialDeriv (fun y => a * h (c • y)) i) x =
        a * c ^ (α.length + 1) * wordDeriv α (spatialDeriv h i) (c • x)
      rw [show spatialDeriv (fun y => a * h (c • y)) i =
        (fun y => (a * c) * spatialDeriv h i (c • y)) by
          funext y
          rw [hsp y]
          ring]
      rw [show wordDeriv α (fun y => (a * c) * spatialDeriv h i (c • y)) =
        (fun y => (a * c) * c ^ α.length * wordDeriv α (spatialDeriv h i) (c • y))
        from hnext]
      ring

private theorem localSobolevMollify_hasCompactSupport_spatialDeriv {h : Vec3 → ℝ}
    (hc : HasCompactSupport h) (i : Fin 3) :
    HasCompactSupport (spatialDeriv h i) := by
  change HasCompactSupport (fun x => (fderiv ℝ h x) (basisVec i))
  exact hc.fderiv_apply (𝕜 := ℝ) (basisVec i)

private theorem localSobolevMollify_wordDeriv_compact {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h) :
    ∀ α : List (Fin 3), HasCompactSupport (wordDeriv α h) := by
  intro α
  induction α generalizing h with
  | nil => simpa [wordDeriv] using hc
  | cons i α ih =>
      exact ih (contDiff_wordDeriv hh [i])
        (localSobolevMollify_hasCompactSupport_spatialDeriv hc i)

private theorem localSobolevMollify_wordDeriv_bound {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (α : List (Fin 3)) : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |wordDeriv α h x| ≤ L := by
  have hcont := (contDiff_wordDeriv hh α).continuous
  have hcompact := localSobolevMollify_wordDeriv_compact hh hc α
  have hcompactNorm : HasCompactSupport (fun x => ‖wordDeriv α h x‖) := hcompact.norm
  obtain ⟨L, hL⟩ := hcont.norm.bounded_above_of_compact_support hcompactNorm
  refine ⟨L, ?_, ?_⟩
  · exact (norm_nonneg (wordDeriv α h 0)).trans (by simpa using hL 0)
  · intro x
    simpa using hL x

@[expose]
noncomputable def localSobolevMollifyProfile : Vec3 → ℝ :=
  Classical.choose (vorticitySpatialCutoff_exists (r := 1) (R := 2) (by norm_num) (by norm_num))

private theorem localSobolevMollifyProfile_spec :
    ContDiff ℝ (⊤ : ℕ∞) localSobolevMollifyProfile ∧
      HasCompactSupport localSobolevMollifyProfile ∧
      (∀ x, vec3EuclideanNorm x ≤ 1 → localSobolevMollifyProfile x = 1) ∧
      (∀ x, 0 ≤ localSobolevMollifyProfile x) ∧
      (∀ x, localSobolevMollifyProfile x ≤ 1) := by
  unfold localSobolevMollifyProfile
  rcases Classical.choose_spec
      (vorticitySpatialCutoff_exists (r := 1) (R := 2) (by norm_num) (by norm_num)) with
    ⟨hs, hc, _, hone, hnonneg, hle⟩
  exact ⟨hs, hc, hone, hnonneg, hle⟩

@[expose]
def localSobolevMollifyScale (n : ℕ) : ℝ :=
  (2 * ((n : ℝ) + 1))⁻¹

@[expose]
def localSobolevMollifyCutoff (n : ℕ) : Vec3 → ℝ :=
  fun x => localSobolevMollifyProfile (localSobolevMollifyScale n • x)

private theorem localSobolevMollifyScale_pos (n : ℕ) :
    0 < localSobolevMollifyScale n := by
  simp only [localSobolevMollifyScale, mul_inv_rev, inv_pos, Nat.ofNat_pos,
    mul_pos_iff_of_pos_right]
  positivity

private theorem localSobolevMollifyScale_le_one (n : ℕ) :
    localSobolevMollifyScale n ≤ 1 := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  dsimp only [localSobolevMollifyScale]
  exact (inv_le_one₀ hden).2 (by nlinarith only [hn])

private theorem localSobolevMollifyCutoff_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (localSobolevMollifyCutoff n) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => localSobolevMollifyProfile (localSobolevMollifyScale n • x))
  exact localSobolevMollifyProfile_spec.1.comp (contDiff_const_smul _)

private theorem localSobolevMollifyCutoff_compact (n : ℕ) :
    HasCompactSupport (localSobolevMollifyCutoff n) := by
  change HasCompactSupport
    (fun x => localSobolevMollifyProfile (localSobolevMollifyScale n • x))
  have hc : localSobolevMollifyScale n ≠ 0 := (localSobolevMollifyScale_pos n).ne'
  exact localSobolevMollifyProfile_spec.2.1.comp_homeomorph
    (Homeomorph.smulOfNeZero _ hc)

private theorem localSobolevMollifyCutoff_nonneg (n : ℕ) (x : Vec3) :
    0 ≤ localSobolevMollifyCutoff n x :=
  localSobolevMollifyProfile_spec.2.2.2.1 _

private theorem localSobolevMollifyCutoff_le_one (n : ℕ) (x : Vec3) :
    localSobolevMollifyCutoff n x ≤ 1 :=
  localSobolevMollifyProfile_spec.2.2.2.2 _

private theorem localSobolevMollifyCutoff_one (n : ℕ) {x : Vec3}
    (hx : vec3EuclideanNorm x ≤ 2 * ((n : ℝ) + 1)) :
    localSobolevMollifyCutoff n x = 1 := by
  rw [localSobolevMollifyCutoff]
  apply localSobolevMollifyProfile_spec.2.2.1
  rw [vec3EuclideanNorm_smul,
    abs_of_pos (localSobolevMollifyScale_pos n)]
  calc
    localSobolevMollifyScale n * vec3EuclideanNorm x ≤
        localSobolevMollifyScale n * (2 * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hx (localSobolevMollifyScale_pos n).le
    _ = 1 := by
      dsimp only [localSobolevMollifyScale]
      field_simp

private theorem localSobolevMollifyCutoff_wordDeriv_bound (m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n (α : List (Fin 3)), α.length ≤ m → ∀ x,
      |wordDeriv α (localSobolevMollifyCutoff n) x| ≤ L := by
  let W := sobolevWords m
  let B : List (Fin 3) → ℝ := fun α => Classical.choose
    (localSobolevMollify_wordDeriv_bound localSobolevMollifyProfile_spec.1
      localSobolevMollifyProfile_spec.2.1 α)
  have hBnonneg (α : List (Fin 3)) : 0 ≤ B α :=
    (Classical.choose_spec
      (localSobolevMollify_wordDeriv_bound localSobolevMollifyProfile_spec.1
        localSobolevMollifyProfile_spec.2.1 α)).1
  have hBbound (α : List (Fin 3)) (x : Vec3) :
      |wordDeriv α localSobolevMollifyProfile x| ≤ B α :=
    (Classical.choose_spec
      (localSobolevMollify_wordDeriv_bound localSobolevMollifyProfile_spec.1
        localSobolevMollifyProfile_spec.2.1 α)).2 x
  refine ⟨∑ α ∈ W, B α, ?_, ?_⟩
  · exact Finset.sum_nonneg fun α hα => hBnonneg α
  · intro n α hα x
    have hαW : α ∈ W := (mem_sobolevWords).2 hα
    have hscale := localSobolevMollify_wordDeriv_scale
      localSobolevMollifyProfile_spec.1 1 (localSobolevMollifyScale n) α
    have hscaleX : wordDeriv α
        (fun x => localSobolevMollifyProfile (localSobolevMollifyScale n • x)) x =
        localSobolevMollifyScale n ^ α.length *
          wordDeriv α localSobolevMollifyProfile (localSobolevMollifyScale n • x) := by
      simpa using congrFun hscale x
    rw [show localSobolevMollifyCutoff n =
      (fun x => localSobolevMollifyProfile (localSobolevMollifyScale n • x)) by rfl,
      hscaleX]
    have hc : 0 ≤ localSobolevMollifyScale n := (localSobolevMollifyScale_pos n).le
    have hc1 : localSobolevMollifyScale n ≤ 1 := localSobolevMollifyScale_le_one n
    rw [abs_mul, abs_pow, abs_of_nonneg hc]
    calc
      localSobolevMollifyScale n ^ α.length *
          |wordDeriv α localSobolevMollifyProfile
            (localSobolevMollifyScale n • x)| ≤ B α := by
        exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hc hc1)).trans
          (hBbound α _)
      _ ≤ ∑ β ∈ W, B β := Finset.single_le_sum
        (fun β _ => hBnonneg β) hαW

private theorem localSobolevMollify_wordDeriv_sub_apply
    (α : List (Fin 3)) {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec3) :
    wordDeriv α (f - g) x =
      wordDeriv α f x - wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hsub : spatialDeriv (fun y => f y - g y) j =
          fun y => spatialDeriv f j y - spatialDeriv g j y := by
        funext y
        have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
          (fderiv_fun_sub ((hf.differentiable (by simp)) y)
            ((hg.differentiable (by simp)) y))
        simpa [spatialDeriv] using h
      change wordDeriv α (spatialDeriv (fun y => f y - g y) j) x = _
      rw [hsub]
      have hfa : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_wordDeriv hf [j]
      have hga : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_wordDeriv hg [j]
      exact ih hfa hga

private theorem localSobolevMollify_wordDeriv_zero (α : List (Fin 3)) :
    wordDeriv α (fun _ : Vec3 => 0) = fun _ => 0 := by
  induction α with
  | nil => rfl
  | cons j α ih =>
      simp only [wordDeriv]
      rw [show spatialDeriv (fun _ : Vec3 => 0) j = fun _ => 0 by
        funext x
        simp [spatialDeriv]]
      exact ih

private theorem localSobolevMollify_wordDeriv_one (α : List (Fin 3)) :
    wordDeriv α (fun _ : Vec3 => 1) =
      fun _ => if α = [] then 1 else 0 := by
  cases α with
  | nil => simp [wordDeriv]
  | cons j α =>
      simp only [wordDeriv]
      rw [show spatialDeriv (fun _ : Vec3 => 1) j = fun _ => 0 by
        funext x
        simp [spatialDeriv], localSobolevMollify_wordDeriv_zero]
      simp

private theorem localSobolevMollify_wordDeriv_eq_of_eventuallyEq
    {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x : Vec3}
    (hfg : f =ᶠ[𝓝 x] g) (α : List (Fin 3)) :
    wordDeriv α f x = wordDeriv α g x := by
  induction α generalizing f g with
  | nil => exact hfg.self_of_nhds
  | cons j α ih =>
      have hfd : fderiv ℝ f =ᶠ[𝓝 x] fderiv ℝ g := hfg.fderiv (𝕜 := ℝ)
      have hsp : spatialDeriv f j =ᶠ[𝓝 x] spatialDeriv g j := by
        filter_upwards [hfd] with y hy
        exact congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hy
      have hfa : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_wordDeriv hf [j]
      have hga : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_wordDeriv hg [j]
      exact ih hfa hga hsp

private theorem localSobolevMollifyCutoff_deriv_zero (n : ℕ) {x : Vec3}
    (hx : vec3EuclideanNorm x ≤ (n : ℝ) + 1)
    (α : List (Fin 3)) (hα : α ≠ []) :
    wordDeriv α (localSobolevMollifyCutoff n) x = 0 := by
  have hball : IsOpen {y : Vec3 | vec3EuclideanNorm y < 2 * ((n : ℝ) + 1)} :=
    isOpen_lt continuous_vec3EuclideanNorm continuous_const
  have hxball : x ∈ {y : Vec3 | vec3EuclideanNorm y < 2 * ((n : ℝ) + 1)} := by
    change vec3EuclideanNorm x < 2 * ((n : ℝ) + 1)
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith only [hx, hn]
  have hnear := hball.mem_nhds hxball
  have hconst : localSobolevMollifyCutoff n =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hnear] with y hy
    exact localSobolevMollifyCutoff_one n (by simpa using (le_of_lt hy))
  rw [localSobolevMollify_wordDeriv_eq_of_eventuallyEq
    (localSobolevMollifyCutoff_contDiff n) contDiff_const hconst α]
  rw [localSobolevMollify_wordDeriv_one]
  simp [hα]

private theorem localSobolevMollify_wordDeriv_mollify {m : ℕ}
    {D : List (Fin 3) → Vec3 → ℝ}
    (h : IsSobolevFamilyOn m univ (D []) D) {ε : ℝ} (hε : 0 < ε) :
    ∀ α : List (Fin 3), α.length ≤ m →
      wordDeriv α (CKN.mollify (D []) ε hε) = CKN.mollify (D α) ε hε := by
  induction m generalizing D with
  | zero =>
      intro α hα
      cases α with
      | nil => rfl
      | cons j α => simp at hα
  | succ m ih =>
      intro α hα
      cases α with
      | nil => rfl
      | cons j α =>
          have hlen : α.length ≤ m := by simp only [List.length_cons] at hα; omega
          have hdec := (isSobolevFamilyOn_succ_iff.mp h).2 j
          have hshift : IsSobolevFamilyOn m univ (D [j]) (fun β => D (j :: β)) := hdec.2
          have hu : LocallyIntegrable (D []) volume := by
            have hmem : MemLp (D []) 2 volume := by
              simpa only [Measure.restrict_univ] using h.memL2 [] (by simp)
            exact hmem.locallyIntegrable (by norm_num)
          have hgi : LocallyIntegrable (D [j]) volume := by
            have hmem : MemLp (D [j]) 2 volume := by
              simpa only [Measure.restrict_univ] using h.memL2 [j] (by simp)
            exact hmem.locallyIntegrable (by norm_num)
          have hfd (x : Vec3) := CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
            isOpen_univ hu hgi hdec.1 hε (Set.subset_univ (Metric.closedBall x ε))
          have hsp : spatialDeriv (CKN.mollify (D []) ε hε) j =
              CKN.mollify (D [j]) ε hε := by
            funext x
            simpa [spatialDeriv] using hfd x
          rw [wordDeriv, hsp]
          exact ih (D := fun β => D (j :: β)) hshift α hlen

@[expose]
def localSobolevMollifyFamily {ι : Type*} [Fintype ι]
    (f : ι → Vec3 → ℝ) (ε : ℝ) (hε : 0 < ε) : Vec3 → ι → ℝ :=
  fun x i => CKN.mollify (f i) ε hε x

private theorem localSobolevMollify_toLp_norm {ι : Type*} [Fintype ι]
    (v : ι → ℝ) :
    ‖WithLp.toLp 2 v‖ = Real.sqrt (∑ i, v i ^ 2) := by
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

private theorem localSobolevMollifyFamily_norm_le {ι : Type*} [Fintype ι]
    {f : ι → Vec3 → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hmem : MemLp (fun x => WithLp.toLp 2 (fun i => f i x)) 2 volume)
    {M : ℝ}
    (hbound : ∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M)
    (x : Vec3) :
    Real.sqrt (∑ i, localSobolevMollifyFamily f ε hε x i ^ 2) ≤ M := by
  let G : Vec3 → WithLp 2 (ι → ℝ) := fun y => WithLp.toLp 2 (fun i => f i y)
  let ρ : Vec3 → ℝ := CKN.mollifier ε hε
  let L : ℝ →L[ℝ] WithLp 2 (ι → ℝ) →L[ℝ] WithLp 2 (ι → ℝ) :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hGloc : LocallyIntegrable G volume := by
    simpa [G] using hmem.locallyIntegrable (by norm_num)
  have hconv : ConvolutionExists ρ G L volume := by
    exact (CKN.mollifier_hasCompactSupport hε).convolutionExists_left
      (L := L) (CKN.mollifier_contDiff hε (n := 0)).continuous hGloc
  let q : WithLp 2 (ι → ℝ) := convolution ρ G L volume x
  have hcoord (i : ι) :
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : ι => ℝ) i) q =
        CKN.mollify (f i) ε hε x := by
    change (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : ι => ℝ) i)
        (convolution ρ G L volume x) = _
    rw [convolution_def]
    have hmap := (PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : ι => ℝ) i).integral_comp_comm (hconv x)
    rw [hmap.symm]
    simp [G, L, ρ, CKN.mollify, convolution_def, PiLp.proj_apply,
      ContinuousLinearMap.lsmul_apply]
  have hqof : WithLp.ofLp q = localSobolevMollifyFamily f ε hε x := by
    funext i
    simpa [q, localSobolevMollifyFamily, PiLp.proj_apply] using hcoord i
  have hqnorm : ‖q‖ =
      Real.sqrt (∑ i, localSobolevMollifyFamily f ε hε x i ^ 2) := by
    calc
      ‖q‖ = ‖WithLp.toLp 2 (WithLp.ofLp q)‖ := by simp
      _ = ‖WithLp.toLp 2 (localSobolevMollifyFamily f ε hε x)‖ := by rw [hqof]
      _ = Real.sqrt (∑ i, localSobolevMollifyFamily f ε hε x i ^ 2) :=
        localSobolevMollify_toLp_norm _
  let qnorm : Vec3 → ℝ := fun y => Real.sqrt (∑ i, f i y ^ 2)
  have hqnormMem : MemLp qnorm 2 volume := by
    simpa [qnorm, G, localSobolevMollify_toLp_norm] using hmem.norm
  have hqnormLoc : LocallyIntegrable qnorm volume := hqnormMem.locallyIntegrable (by norm_num)
  have hkernelInt : Integrable ρ volume :=
    (CKN.mollifier_contDiff hε (n := 0)).continuous.integrable_of_hasCompactSupport
      (CKN.mollifier_hasCompactSupport hε)
  have hconvNorm : ConvolutionExists ρ qnorm
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    (CKN.mollifier_hasCompactSupport hε).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (CKN.mollifier_contDiff hε (n := 0)).continuous hqnormLoc
  have hboundShift : ∀ᵐ y ∂volume, qnorm (x - y) ≤ M :=
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hbound
  have hleftInt : Integrable (fun y => ρ y * qnorm (x - y)) volume := by
    exact (hconvNorm x).integrable
  have hrightInt : Integrable (fun y => ρ y * M) volume := hkernelInt.mul_const M
  have hscalar : CKN.mollify qnorm ε hε x ≤ M := by
    change (∫ y, ρ y * qnorm (x - y) ∂volume) ≤ M
    calc
      (∫ y, ρ y * qnorm (x - y) ∂volume) ≤ ∫ y, ρ y * M ∂volume :=
        integral_mono_ae hleftInt hrightInt
          (hboundShift.mono fun y hy => mul_le_mul_of_nonneg_left hy
            (CKN.mollifier_nonneg hε y))
      _ = M := by
        rw [integral_mul_const, CKN.mollifier_integral_one]
        ring
  calc
    Real.sqrt (∑ i, localSobolevMollifyFamily f ε hε x i ^ 2) = ‖q‖ := hqnorm.symm
    _ ≤ ∫ y, ‖ρ y • G (x - y)‖ ∂volume := by
      rw [show q = ∫ y, ρ y • G (x - y) ∂volume by rfl]
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ρ y * qnorm (x - y) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (CKN.mollifier_nonneg hε y)]
      change CKN.mollifier ε hε y *
          ‖WithLp.toLp 2 (fun i => f i (x - y))‖ =
        CKN.mollifier ε hε y * Real.sqrt (∑ i, f i (x - y) ^ 2)
      rw [localSobolevMollify_toLp_norm]
    _ = CKN.mollify qnorm ε hε x := by
      rw [CKN.mollify, convolution_def]
      rfl
    _ ≤ M := hscalar

@[expose]
def localSobolevMollifyTail (n : ℕ) : Set Vec3 :=
  {x | (n : ℝ) + 1 < vec3EuclideanNorm x}

private theorem localSobolevMollifyTail_open (n : ℕ) :
    IsOpen (localSobolevMollifyTail n) := by
  change IsOpen {x : Vec3 | (n : ℝ) + 1 < vec3EuclideanNorm x}
  exact isOpen_lt continuous_const continuous_vec3EuclideanNorm

private theorem localSobolevMollifyTail_measurable (n : ℕ) :
    MeasurableSet (localSobolevMollifyTail n) :=
  (localSobolevMollifyTail_open n).measurableSet

private theorem localSobolevMollify_tail_integral_tendsto
    {m : ℕ} {D : List (Fin 3) → Vec3 → ℝ}
    (h : IsSobolevFamilyOn m univ (D []) D) (α : List (Fin 3))
    (hα : α.length ≤ m) :
    Tendsto (fun n => ∫ x in localSobolevMollifyTail n, D α x ^ 2) atTop (𝓝 0) := by
  have hDmem : MemLp (D α) 2 volume := by
    simpa only [Measure.restrict_univ] using h.memL2 α hα
  have hDint : Integrable (fun x => D α x ^ 2) volume := hDmem.integrable_sq
  let F : ℕ → Vec3 → ℝ := fun n =>
    (localSobolevMollifyTail n).indicator (fun x => D α x ^ 2)
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    hDint.aestronglyMeasurable.indicator (localSobolevMollifyTail_measurable n)
  have hFint (n : ℕ) : Integrable (F n) volume :=
    hDint.indicator (localSobolevMollifyTail_measurable n)
  have hbound (n : ℕ) : ∀ᵐ x ∂volume, ‖F n x‖ ≤ D α x ^ 2 := by
    apply ae_of_all
    intro x
    by_cases hx : x ∈ localSobolevMollifyTail n
    · simp [F, hx, Real.norm_eq_abs]
    · simp only [hx, not_false_eq_true, indicator_of_notMem, norm_zero, F]
      exact sq_nonneg (D α x)
  have hpoint (x : Vec3) : Tendsto (fun n => F n x) atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (vec3EuclideanNorm x)
    have hNeventually : ∀ᶠ n : ℕ in atTop, N ≤ n := eventually_ge_atTop N
    have hzero : ∀ᶠ n : ℕ in atTop, F n x = 0 := by
      filter_upwards [hNeventually] with n hn
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hxnot : x ∉ localSobolevMollifyTail n := by
        change ¬ ((n : ℝ) + 1 < vec3EuclideanNorm x)
        have hxbound : vec3EuclideanNorm x ≤ (N : ℝ) := hN
        linarith only [hxbound, hn']
      simp [F, hxnot]
    exact tendsto_const_nhds.congr' (hzero.mono fun n hn => hn.symm)
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun x => D α x ^ 2) hFmeas hDint hbound (ae_of_all _ hpoint)
  have hset (n : ℕ) :
      ∫ x, F n x ∂volume = ∫ x in localSobolevMollifyTail n, D α x ^ 2 := by
    exact integral_indicator (localSobolevMollifyTail_measurable n)
  simpa only [hset, integral_zero] using hDCT

private theorem localSobolevMollify_tail_normSq_tendsto
    {m : ℕ} {D : List (Fin 3) → Vec3 → ℝ}
    (h : IsSobolevFamilyOn m univ (D []) D) :
    Tendsto (fun n => sobolevNormSqOn m (localSobolevMollifyTail n) D)
      atTop (𝓝 0) := by
  let W := sobolevWords m
  have hsum : Tendsto
      (fun n => ∑ α ∈ W, ∫ x in localSobolevMollifyTail n, D α x ^ 2)
      atTop (𝓝 (∑ α ∈ W, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro α hα
    exact localSobolevMollify_tail_integral_tendsto h α
      (mem_sobolevWords.mp (show α ∈ sobolevWords m from by simpa [W] using hα))
  simpa [sobolevNormSqOn, W] using hsum

private theorem localSobolevMollify_tendsto_eLpNorm_of_integral_sq
    {f : ℕ → Vec3 → ℝ} (hf : ∀ n, MemLp (f n) 2 volume)
    (h : Tendsto (fun n => ∫ x, f n x ^ 2 ∂volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0) := by
  have hformula (n : ℕ) :
      eLpNorm (f n) 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, f n x ^ 2 ∂volume)) := by
    rw [(hf n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 1
    have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [htwo, Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]
  have hcont : Tendsto
      (fun n => ENNReal.ofReal (Real.sqrt (∫ x, f n x ^ 2 ∂volume))) atTop
      (𝓝 (ENNReal.ofReal (Real.sqrt 0))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_sqrt.tendsto 0).comp h)
  rw [Real.sqrt_zero, ENNReal.ofReal_zero] at hcont
  exact hcont.congr fun n => (hformula n).symm

private theorem localSobolevMollify_leibniz_add_coeff
    (α : List (Fin 3)) (A B : List (Fin 3) → Vec3 → ℝ)
    (D : List (Fin 3) → Vec3 → ℝ) :
    ∀ x, sobolevLeibnizFamily α (fun β x => A β x + B β x) D x =
      sobolevLeibnizFamily α A D x + sobolevLeibnizFamily α B D x := by
  induction α generalizing A B D with
  | nil => intro x; simp [sobolevLeibnizFamily]; ring
  | cons j α ih =>
      intro x
      simp only [sobolevLeibnizFamily]
      rw [ih (fun β y => A (j :: β) y) (fun β y => B (j :: β) y) D,
        ih A B (fun β y => D (j :: β) y)]
      ring

private theorem localSobolevMollify_leibniz_zero_coeff
    (α : List (Fin 3)) (D : List (Fin 3) → Vec3 → ℝ) (x : Vec3) :
    sobolevLeibnizFamily α (fun _ _ => (0 : ℝ)) D x = 0 := by
  induction α generalizing D with
  | nil => simp [sobolevLeibnizFamily]
  | cons j α ih => simp [sobolevLeibnizFamily, ih]

private theorem localSobolevMollify_leibniz_one_coeff
    (α : List (Fin 3)) (D : List (Fin 3) → Vec3 → ℝ) (x : Vec3) :
    sobolevLeibnizFamily α (fun β _ => if β = [] then 1 else 0) D x = D α x := by
  induction α generalizing D with
  | nil => simp [sobolevLeibnizFamily]
  | cons j α ih =>
      simp only [sobolevLeibnizFamily]
      rw [show (fun β y => if j :: β = [] then 1 else 0) =
        (fun _ _ => (0 : ℝ)) by funext β y; simp,
        localSobolevMollify_leibniz_zero_coeff α D x,
        ih (fun β y => D (j :: β) y)]
      simp

@[expose]
def localSobolevMollifyRemainder (n : ℕ) : Vec3 → ℝ :=
  (fun _ : Vec3 => 1) - localSobolevMollifyCutoff n

private theorem localSobolevMollifyRemainder_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (localSobolevMollifyRemainder n) := by
  exact contDiff_const.sub (localSobolevMollifyCutoff_contDiff n)

private theorem localSobolevMollifyRemainder_coeff_bound (m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n (α : List (Fin 3)), α.length ≤ m → ∀ x,
      |wordDeriv α (localSobolevMollifyRemainder n) x| ≤ L := by
  obtain ⟨L, hL, hbound⟩ := localSobolevMollifyCutoff_wordDeriv_bound m
  refine ⟨L + 1, by positivity, ?_⟩
  intro n α hα x
  have hsub := localSobolevMollify_wordDeriv_sub_apply
    (f := fun _ : Vec3 => (1 : ℝ)) (g := localSobolevMollifyCutoff n) α
    (contDiff_const) (localSobolevMollifyCutoff_contDiff n) x
  have hone := congrFun (localSobolevMollify_wordDeriv_one α) x
  rw [show localSobolevMollifyRemainder n =
      (fun _ : Vec3 => 1) - localSobolevMollifyCutoff n by rfl, hsub, hone]
  have hconst : |(if α = [] then (1 : ℝ) else 0)| ≤ 1 := by
    by_cases hαnil : α = [] <;> simp [hαnil]
  have htriangle :
      |(if α = [] then (1 : ℝ) else 0) -
        wordDeriv α (localSobolevMollifyCutoff n) x| ≤
      |if α = [] then (1 : ℝ) else 0| +
        |wordDeriv α (localSobolevMollifyCutoff n) x| := by
    simpa using abs_sub_le (if α = [] then (1 : ℝ) else 0) 0
      (wordDeriv α (localSobolevMollifyCutoff n) x)
  exact htriangle.trans (by
    have hb := hbound n α hα x
    calc
      |if α = [] then (1 : ℝ) else 0| +
          |wordDeriv α (localSobolevMollifyCutoff n) x| ≤ 1 + L := by
        exact add_le_add hconst hb
      _ = L + 1 := by ring)

private theorem localSobolevMollifyRemainder_deriv_zero (n : ℕ) {x : Vec3}
    (hx : x ∉ localSobolevMollifyTail n) (α : List (Fin 3)) :
    wordDeriv α (localSobolevMollifyRemainder n) x = 0 := by
  have hxball : vec3EuclideanNorm x ≤ (n : ℝ) + 1 := by
    change ¬ ((n : ℝ) + 1 < vec3EuclideanNorm x) at hx
    exact le_of_not_gt hx
  have hsub := localSobolevMollify_wordDeriv_sub_apply
    (f := fun _ : Vec3 => (1 : ℝ)) (g := localSobolevMollifyCutoff n) α
    contDiff_const (localSobolevMollifyCutoff_contDiff n) x
  have hone := congrFun (localSobolevMollify_wordDeriv_one α) x
  rw [show localSobolevMollifyRemainder n =
      (fun _ : Vec3 => 1) - localSobolevMollifyCutoff n by rfl, hsub, hone]
  by_cases hnil : α = []
  · subst α
    rw [show wordDeriv [] (localSobolevMollifyCutoff n) x =
      localSobolevMollifyCutoff n x by rfl]
    rw [localSobolevMollifyCutoff_one n (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have htwice : (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by nlinarith only [hn]
      exact hxball.trans htwice)]
    simp
  · simp only [hnil, ↓reduceIte, zero_sub, neg_eq_zero]
    rw [localSobolevMollifyCutoff_deriv_zero n hxball α hnil]

private theorem localSobolevMollify_cutoff_error_tendsto
    {m : ℕ} {D : List (Fin 3) → Vec3 → ℝ}
    (h : IsSobolevFamilyOn m univ (D []) D) :
    ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun n => eLpNorm
        (fun x => sobolevLeibnizFamily α
          (fun β => wordDeriv β (localSobolevMollifyRemainder n)) D x)
        2 volume) atTop (𝓝 0) := by
  obtain ⟨C, hC, hproduct⟩ := sobolevLeibnizFamily_normSq_le m
  obtain ⟨L, hL, hcoeff⟩ := localSobolevMollifyRemainder_coeff_bound m
  have htail := localSobolevMollify_tail_normSq_tendsto h
  have hprodTendsto : Tendsto
      (fun n => C * L ^ 2 * sobolevNormSqOn m (localSobolevMollifyTail n) D)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul htail : Tendsto
        (fun n => (C * L ^ 2) * sobolevNormSqOn m (localSobolevMollifyTail n) D)
        atTop (𝓝 ((C * L ^ 2) * 0)))
  have herrorBound (n : ℕ) :
      sobolevNormSqOn m univ
        (fun β => sobolevLeibnizFamily β
          (fun γ => wordDeriv γ (localSobolevMollifyRemainder n)) D) ≤
      C * L ^ 2 * sobolevNormSqOn m (localSobolevMollifyTail n) D := by
    have hh := hproduct (localSobolevMollifyTail n) univ
      (fun β => wordDeriv β (localSobolevMollifyRemainder n)) D L
    have hh' := hh (localSobolevMollifyTail_measurable n) MeasurableSet.univ
      (Set.subset_univ _) (fun β hβ x => hcoeff n β hβ x)
      (fun β hβ x hx => localSobolevMollifyRemainder_deriv_zero n hx β)
      (fun β hβ => (((contDiff_wordDeriv
        (localSobolevMollifyRemainder_contDiff n) β).continuous).aestronglyMeasurable))
      (fun β hβ => by simpa only [Measure.restrict_univ] using h.memL2 β hβ)
    calc
      _ ≤ C * L ^ 2 * sobolevNormSqOn m
          (localSobolevMollifyTail n ∩ univ) D := hh'
      _ = C * L ^ 2 * sobolevNormSqOn m (localSobolevMollifyTail n) D := by
        rw [Set.inter_univ]
  have herrorSq (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun n => ∫ x,
        (sobolevLeibnizFamily α
          (fun β => wordDeriv β (localSobolevMollifyRemainder n)) D x) ^ 2 ∂volume)
        atTop (𝓝 0) := by
    let E : ℕ → List (Fin 3) → Vec3 → ℝ := fun n β x =>
      sobolevLeibnizFamily β
        (fun γ => wordDeriv γ (localSobolevMollifyRemainder n)) D x
    have hnonneg (n : ℕ) : 0 ≤ sobolevNormSqOn m univ (E n) := by
      unfold sobolevNormSqOn
      apply Finset.sum_nonneg
      intro β hβ
      exact integral_nonneg fun x => sq_nonneg (E n β x)
    have hS : Tendsto (fun n => sobolevNormSqOn m univ (E n)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprodTendsto
        (Eventually.of_forall hnonneg) (Eventually.of_forall fun n => herrorBound n)
    have hαW : α ∈ sobolevWords m := mem_sobolevWords.mpr hα
    have hle (n : ℕ) :
        ∫ x, (E n α x) ^ 2 ∂volume ≤ sobolevNormSqOn m univ (E n) := by
      rw [sobolevNormSqOn, Measure.restrict_univ]
      exact Finset.single_le_sum
        (f := fun β => ∫ x, E n β x ^ 2 ∂volume)
        (fun β hβ => integral_nonneg fun x => sq_nonneg (E n β x)) hαW
    have hnonnegSq (n : ℕ) : 0 ≤ ∫ x, (E n α x) ^ 2 ∂volume :=
      integral_nonneg fun x => sq_nonneg (E n α x)
    simpa only [E] using
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hS
        (Eventually.of_forall hnonnegSq)
        (Eventually.of_forall hle))
  intro α hα
  let err : ℕ → Vec3 → ℝ := fun n x =>
    sobolevLeibnizFamily α
      (fun β => wordDeriv β (localSobolevMollifyRemainder n)) D x
  obtain ⟨Lχ, _, hcutBound⟩ := localSobolevMollifyCutoff_wordDeriv_bound m
  have hmem (n : ℕ) : MemLp (err n) 2 volume := by
    have hcut :=
      h.smooth_mul isOpen_univ (localSobolevMollifyCutoff_contDiff n)
        (fun β hβ => ⟨Lχ, hcutBound n β hβ⟩)
    have hDmem : MemLp (D α) 2 volume := by
      simpa only [Measure.restrict_univ] using h.memL2 α hα
    have hcutmem : MemLp
        (sobolevLeibnizFamily α
          (fun γ => wordDeriv γ (localSobolevMollifyCutoff n)) D) 2 volume := by
      simpa only [Measure.restrict_univ] using hcut.memL2 α hα
    have hidentity : ∀ x, err n x = D α x -
        sobolevLeibnizFamily α
          (fun γ => wordDeriv γ (localSobolevMollifyCutoff n)) D x := by
      intro x
      have hcoef (β : List (Fin 3)) (y : Vec3) :
          wordDeriv β (localSobolevMollifyRemainder n) y +
            wordDeriv β (localSobolevMollifyCutoff n) y =
          (if β = [] then (1 : ℝ) else 0) := by
        have hs := localSobolevMollify_wordDeriv_sub_apply
          (f := fun _ : Vec3 => (1 : ℝ)) (g := localSobolevMollifyCutoff n) β
          contDiff_const (localSobolevMollifyCutoff_contDiff n) y
        have ho := congrFun (localSobolevMollify_wordDeriv_one β) y
        rw [show localSobolevMollifyRemainder n =
          (fun _ : Vec3 => 1) - localSobolevMollifyCutoff n by rfl, hs, ho]
        ring
      have hadd := localSobolevMollify_leibniz_add_coeff α
        (fun β y => wordDeriv β (localSobolevMollifyRemainder n) y)
        (fun β y => wordDeriv β (localSobolevMollifyCutoff n) y) D x
      have hcoefEq : (fun β y => wordDeriv β (localSobolevMollifyRemainder n) y +
          wordDeriv β (localSobolevMollifyCutoff n) y) =
          (fun β y => if β = [] then (1 : ℝ) else 0) := by
        funext β y
        exact hcoef β y
      have hone := localSobolevMollify_leibniz_one_coeff α D x
      change sobolevLeibnizFamily α
        (fun β => wordDeriv β (localSobolevMollifyRemainder n)) D x = _
      rw [← hone]
      rw [← hcoefEq]
      rw [hadd]
      ring
    exact (memLp_congr_ae (ae_of_all _ fun x => (hidentity x).symm)).1
      (hDmem.sub hcutmem)
  have hsq := herrorSq α hα
  have hnorm := localSobolevMollify_tendsto_eLpNorm_of_integral_sq
    (fun n => hmem n) (by simpa [err] using hsq)
  simpa [err] using hnorm

private theorem localSobolevMollify_cutoff_uniform_bound
    {ι : Type*} [Fintype ι] (χ : Vec3 → ℝ)
    (D0 f : ι → Vec3 → ℝ) (M : ℝ)
    (hzero : ∀ᵐ x ∂volume, ∀ i, D0 i x = f i x)
    (hχ : ∀ x, |χ x| ≤ 1)
    (hM : ∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) :
    ∀ᵐ x ∂volume, Real.sqrt (∑ i, (χ x * D0 i x) ^ 2) ≤ M := by
  filter_upwards [hM, hzero] with x hx hfx
  have hsum : ∑ i, (χ x * D0 i x) ^ 2 = χ x ^ 2 * ∑ i, f i x ^ 2 := by
    simp only [mul_pow]
    rw [← Finset.mul_sum]
    apply congrArg
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfx i]
  rw [hsum, Real.sqrt_mul (sq_nonneg (χ x)), Real.sqrt_sq_eq_abs]
  calc
    |χ x| * Real.sqrt (∑ i, f i x ^ 2) ≤
        1 * Real.sqrt (∑ i, f i x ^ 2) :=
      mul_le_mul_of_nonneg_right (hχ x) (Real.sqrt_nonneg _)
    _ ≤ M := by simpa using hx

private theorem localSobolevMollify_approximation_from_errors
    {ι : Type*} {m : ℕ}
    (D : List (Fin 3) → ι → Vec3 → ℝ)
    (cutD : ℕ → ι → List (Fin 3) → Vec3 → ℝ)
    (g : ℕ → ι → Vec3 → ℝ) (delta : ℕ → ℝ)
    (hmollError : ∀ n i α, α.length ≤ m →
      eLpNorm (wordDeriv α (g n i) - cutD n i α) 2 volume ≤
        ENNReal.ofReal (delta n))
    (hcutError : ∀ i α, α.length ≤ m →
      Tendsto (fun n => eLpNorm (D α i - cutD n i α) 2 volume) atTop (𝓝 0))
    (hdeltaENN : Tendsto (fun n => ENNReal.ofReal (delta n)) atTop (𝓝 0)) :
    ∀ i α, α.length ≤ m →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D α i) 2 volume)
        atTop (𝓝 0) := by
  intro i α hα
  have hcutNeg : Tendsto
      (fun n => eLpNorm (cutD n i α - D α i) 2 volume) atTop (𝓝 0) := by
    have heq (n : ℕ) :
        eLpNorm (cutD n i α - D α i) 2 volume =
          eLpNorm (D α i - cutD n i α) 2 volume := by
      calc
        eLpNorm (cutD n i α - D α i) 2 volume =
            eLpNorm (-(D α i - cutD n i α)) 2 volume := by
          apply eLpNorm_congr_ae
          filter_upwards [] with x
          change cutD n i α x - D α i x = -(D α i x - cutD n i α x)
          ring
        _ = _ := by rw [eLpNorm_neg]
    exact (hcutError i α hα).congr fun n => (heq n).symm
  have hupper : Tendsto
      (fun n => ENNReal.ofReal (delta n) + eLpNorm (cutD n i α - D α i) 2 volume)
      atTop (𝓝 0) := by
    simpa using hdeltaENN.add hcutNeg
  have hbound (n : ℕ) :
      eLpNorm (wordDeriv α (g n i) - D α i) 2 volume ≤
        ENNReal.ofReal (delta n) + eLpNorm (cutD n i α - D α i) 2 volume := by
    have htriangle :
        eLpNorm (wordDeriv α (g n i) - D α i) 2 volume ≤
          eLpNorm (wordDeriv α (g n i) - cutD n i α) 2 volume +
            eLpNorm (cutD n i α - D α i) 2 volume := by
      calc
        _ = eLpNorm ((fun x => wordDeriv α (g n i) x - cutD n i α x) +
            (fun x => cutD n i α x - D α i x)) 2 volume := by
          apply eLpNorm_congr_ae
          filter_upwards [] with x
          change wordDeriv α (g n i) x - D α i x =
            (wordDeriv α (g n i) x - cutD n i α x) +
              (cutD n i α x - D α i x)
          ring
        _ ≤ _ := eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact htriangle.trans (add_le_add (hmollError n i α hα) le_rfl)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hbound)

/-- Every finite whole-space Sobolev family has smooth compactly supported
approximations in all represented derivatives, with the same vector-valued
essential supremum bound. -/
theorem sobolevFamily_smooth_approx {ι : Type*} [Fintype ι] {m : ℕ}
    {f : ι → Vec3 → ℝ}
    {D : List (Fin 3) → ι → Vec3 → ℝ}
    (h : ∀ i, IsSobolevFamilyOn m univ (f i) (D · i)) :
    ∃ g : ℕ → ι → Vec3 → ℝ,
      (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i)) ∧
      (∀ n i, HasCompactSupport (g n i)) ∧
      (∀ i (α : List (Fin 3)), α.length ≤ m →
        Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D α i) 2 volume)
          atTop (𝓝 0)) ∧
      ∀ M : ℝ, (∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) →
        ∀ n x, Real.sqrt (∑ i, g n i x ^ 2) ≤ M := by
  let χ : ℕ → Vec3 → ℝ := localSobolevMollifyCutoff
  let cutBase : ℕ → ι → Vec3 → ℝ := fun n i x => χ n x * D [] i x
  let cutD : ℕ → ι → List (Fin 3) → Vec3 → ℝ := fun n i α =>
    sobolevLeibnizFamily α (fun β => wordDeriv β (χ n)) (D · i)
  let eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let delta : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hcutBoundUniform : ∃ L : ℝ, 0 ≤ L ∧ ∀ n (α : List (Fin 3)), α.length ≤ m → ∀ x,
      |wordDeriv α (χ n) x| ≤ L := by
    simpa only [χ] using localSobolevMollifyCutoff_wordDeriv_bound m
  obtain ⟨Lχ, _, hcutBound⟩ := hcutBoundUniform
  have hDrep (i : ι) : IsSobolevFamilyOn m univ (D [] i) (D · i) := by
    exact (h i).congr_ae (h i).zero.symm (fun α hα => Filter.Eventually.of_forall fun x => rfl)
  have hcut (n : ℕ) (i : ι) :
      IsSobolevFamilyOn m univ (cutBase n i) (cutD n i) := by
    change IsSobolevFamilyOn m univ
      (fun x => localSobolevMollifyCutoff n x * D [] i x)
      (fun α => sobolevLeibnizFamily α
        (fun β => wordDeriv β (localSobolevMollifyCutoff n)) (D · i))
    exact (hDrep i).smooth_mul isOpen_univ (localSobolevMollifyCutoff_contDiff n)
      (fun α hα => ⟨Lχ, hcutBound n α hα⟩)
  have hbaseEq (n : ℕ) (i : ι) : cutD n i [] = cutBase n i := by
    funext x
    change wordDeriv [] (χ n) x * D [] i x = χ n x * D [] i x
    rfl
  have hcutLoc (n : ℕ) (i : ι) : LocallyIntegrable (cutBase n i) volume := by
    have hmem : MemLp (cutBase n i) 2 volume := by
      simpa only [Measure.restrict_univ, hbaseEq] using (hcut n i).memL2 [] (by simp)
    exact hmem.locallyIntegrable (by norm_num)
  have hcutCompact (n : ℕ) (i : ι) : HasCompactSupport (cutBase n i) := by
    change HasCompactSupport (fun x => χ n x * D [] i x)
    exact (localSobolevMollifyCutoff_compact n).mul_right
  have hcutDmem (n : ℕ) (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      MemLp (cutD n i α) 2 volume := by
    simpa only [Measure.restrict_univ] using (hcut n i).memL2 α hα
  have hepsPos (k : ℕ) : 0 < eps k := by
    simp only [one_div, inv_pos, eps]
    positivity
  have hepsLim : Tendsto eps atTop (𝓝 0) := by
    change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hdeltaPos (n : ℕ) : 0 < delta n := by
    simp only [one_div, inv_pos, delta]
    positivity
  have hdeltaLim : Tendsto delta atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let W := sobolevWords m
  let P : Finset (ι × List (Fin 3)) := Finset.univ.product W
  let mollErr (n k : ℕ) (p : ι × List (Fin 3)) : ℝ≥0∞ :=
    eLpNorm (CKN.mollify (cutD n p.1 p.2) (eps k) (hepsPos k) -
      cutD n p.1 p.2) 2 volume
  have hcomponentMollify (n : ℕ) (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun k => mollErr n k (i, α)) atTop (𝓝 0) := by
    change Tendsto (fun k => eLpNorm
      (CKN.mollify (cutD n i α) (eps k) (hepsPos k) - cutD n i α)
      2 volume) atTop (𝓝 0)
    exact CKN.tendsto_eLpNorm_sub_zero_mollify (p := (2 : ℝ≥0∞))
      (by norm_num) ENNReal.coe_ne_top (hcutDmem n i α hα) hepsLim hepsPos
  have hsumMollify (n : ℕ) :
      Tendsto (fun k => ∑ p ∈ P, mollErr n k p) atTop (𝓝 0) := by
    have hsum : Tendsto (fun k => ∑ p ∈ P, mollErr n k p) atTop
        (𝓝 (∑ p ∈ P, (0 : ℝ≥0∞))) := by
      apply tendsto_finsetSum (s := P)
      intro p hp
      have hp' : p ∈ Finset.univ.product W := by simpa only [P] using hp
      have hp'' := Finset.mem_product.mp hp'
      exact hcomponentMollify n p.1 p.2
        (mem_sobolevWords.mp (by simpa only [W] using hp''.2))
    simpa using hsum
  have hselect (n : ℕ) : ∃ k : ℕ, ∑ p ∈ P, mollErr n k p < ENNReal.ofReal (delta n) := by
    have hη : 0 < ENNReal.ofReal (delta n) := ENNReal.ofReal_pos.mpr (hdeltaPos n)
    have hEventually : ∀ᶠ k in atTop, ∑ p ∈ P, mollErr n k p < ENNReal.ofReal (delta n) :=
      (hsumMollify n).eventually (Iio_mem_nhds hη)
    exact hEventually.exists
  let kSel : ℕ → ℕ := fun n => Classical.choose (hselect n)
  have hkSel (n : ℕ) : ∑ p ∈ P, mollErr n (kSel n) p < ENNReal.ofReal (delta n) :=
    Classical.choose_spec (hselect n)
  let epsFinal : ℕ → ℝ := fun n => eps (kSel n)
  have hepsFinalPos (n : ℕ) : 0 < epsFinal n := hepsPos (kSel n)
  let g : ℕ → ι → Vec3 → ℝ := fun n i =>
    CKN.mollify (cutBase n i) (epsFinal n) (hepsFinalPos n)
  have hgSmooth (n : ℕ) (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (g n i) := by
    exact CKN.mollify_contDiff (hepsFinalPos n) (hcutLoc n i) (n := ⊤)
  have hgCompact (n : ℕ) (i : ι) : HasCompactSupport (g n i) := by
    change HasCompactSupport
      ((CKN.mollifier (epsFinal n) (hepsFinalPos n)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] (cutBase n i))
    exact (CKN.mollifier_hasCompactSupport (hepsFinalPos n)).convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hcutCompact n i)
  have hderiv (n : ℕ) (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      wordDeriv α (g n i) = CKN.mollify (cutD n i α)
        (epsFinal n) (hepsFinalPos n) := by
    have hcutDbase : IsSobolevFamilyOn m univ (cutD n i []) (cutD n i) := by
      exact (hcut n i).congr_ae (by
        filter_upwards [] with x
        exact congrFun (hbaseEq n i).symm x)
        (fun β hβ => Filter.Eventually.of_forall fun x => rfl)
    have hmoll := localSobolevMollify_wordDeriv_mollify hcutDbase
      (hepsFinalPos n) α hα
    change wordDeriv α (CKN.mollify (cutBase n i)
      (epsFinal n) (hepsFinalPos n)) = _
    rw [← hbaseEq]
    exact hmoll
  have hmollifyBound (n : ℕ) (p : ι × List (Fin 3)) (hp : p ∈ P) :
      mollErr n (kSel n) p ≤ ENNReal.ofReal (delta n) := by
    have hle := Finset.single_le_sum
      (f := fun q => mollErr n (kSel n) q) (fun q hq => bot_le) hp
    exact hle.trans (hkSel n).le
  have hcutError (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun n => eLpNorm
        (fun x => D α i x - cutD n i α x) 2 volume) atTop (𝓝 0) := by
    have herr := localSobolevMollify_cutoff_error_tendsto
      (m := m) (D := fun β x => D β i x) (hDrep i) α hα
    have heq (n : ℕ) :
        (fun x => D α i x - cutD n i α x) =
          (fun x => sobolevLeibnizFamily α
            (fun β => wordDeriv β (localSobolevMollifyRemainder n)) (D · i) x) := by
      funext x
      have hcoef (β : List (Fin 3)) (y : Vec3) :
          wordDeriv β (localSobolevMollifyRemainder n) y + wordDeriv β (χ n) y =
            (if β = [] then (1 : ℝ) else 0) := by
        have hs := localSobolevMollify_wordDeriv_sub_apply
          (f := fun _ : Vec3 => (1 : ℝ)) (g := χ n) β contDiff_const
          (localSobolevMollifyCutoff_contDiff n) y
        have ho := congrFun (localSobolevMollify_wordDeriv_one β) y
        have hχ : χ n = localSobolevMollifyCutoff n := rfl
        rw [hχ] at hs
        rw [show localSobolevMollifyRemainder n =
          (fun _ : Vec3 => 1) - localSobolevMollifyCutoff n by rfl, hs, ho]
        ring
      have hadd := localSobolevMollify_leibniz_add_coeff α
        (fun β y => wordDeriv β (localSobolevMollifyRemainder n) y)
        (fun β y => wordDeriv β (χ n) y) (D · i) x
      have hone := localSobolevMollify_leibniz_one_coeff α (D · i) x
      have hcoefEq : (fun β y => wordDeriv β (localSobolevMollifyRemainder n) y +
          wordDeriv β (χ n) y) = (fun β y => if β = [] then (1 : ℝ) else 0) := by
        funext β y
        exact hcoef β y
      rw [hcoefEq] at hadd
      change _ = _
      rw [← hone, hadd]
      ring
    rw [show (fun n => eLpNorm (fun x => D α i x - cutD n i α x) 2 volume) =
      (fun n => eLpNorm
        (fun x => sobolevLeibnizFamily α
          (fun β => wordDeriv β (localSobolevMollifyRemainder n)) (D · i) x)
        2 volume) by funext n; rw [heq n]]
    exact herr
  have hdeltaENN : Tendsto (fun n => ENNReal.ofReal (delta n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hdeltaLim
  have hmollError (n : ℕ) (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      eLpNorm (wordDeriv α (g n i) - cutD n i α) 2 volume ≤
        ENNReal.ofReal (delta n) := by
    have hEq : eLpNorm (wordDeriv α (g n i) - cutD n i α) 2 volume =
        mollErr n (kSel n) (i, α) := by
      rw [eLpNorm_congr_ae (ae_of_all _ fun x => by rw [hderiv n i α hα])]
    rw [hEq]
    have hp : (i, α) ∈ P := by
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_univ i, (mem_sobolevWords).2 hα⟩
    exact hmollifyBound n (i, α) hp
  have happrox (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :=
    localSobolevMollify_approximation_from_errors D cutD g delta
      (hmollError · · ·) hcutError hdeltaENN i α hα
  have hbaseMem (n : ℕ) :
      MemLp (fun x => WithLp.toLp 2 (fun i => cutBase n i x)) 2 volume := by
    apply MeasureTheory.memLp_piLp_iff.mpr
    intro i
    simpa only [Measure.restrict_univ, hbaseEq] using (hcut n i).memL2 [] (by simp)
  have hDzero : ∀ᵐ x ∂volume, ∀ i, D [] i x = f i x := by
    rw [ae_all_iff]
    intro i
    simpa only [Set.mem_univ, true_implies] using
      (ae_restrict_iff' (μ := volume) MeasurableSet.univ).1 (h i).zero
  have hbaseBound (n : ℕ) (M : ℝ)
      (hM : ∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) :
      ∀ᵐ x ∂volume, Real.sqrt (∑ i, cutBase n i x ^ 2) ≤ M := by
    have hχ (x : Vec3) : |χ n x| ≤ 1 := by
      rw [abs_of_nonneg (localSobolevMollifyCutoff_nonneg n x)]
      exact localSobolevMollifyCutoff_le_one n x
    exact localSobolevMollify_cutoff_uniform_bound (χ n)
      (fun i x => D [] i x) f M hDzero hχ hM
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro n i
    exact hgSmooth n i
  · intro n i
    exact hgCompact n i
  · exact happrox
  · intro M hM n x
    have hnorm := localSobolevMollifyFamily_norm_le (f := cutBase n)
      (hepsFinalPos n) (hbaseMem n) (hbaseBound n M hM) x
    simpa [g, localSobolevMollifyFamily, epsFinal] using hnorm

end CKN
