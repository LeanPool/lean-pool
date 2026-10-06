/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalDivCurlCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevLeibniz
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGain
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityProductsSmooth

/-!
# The local div–curl estimate from the whole-space estimate

For concentric balls `B_r ⋐ B_R` and `m ∈ {0, 1, 2}`: if `v ∈ H^m(B_R; ℝ³)`,
`div v = 0` and `curl v = ζ ∈ H^m(B_R; ℝ³)`, then
`‖v‖_{H^{m+1}(B_r)} ≤ C (‖ζ‖_{H^m(B_R)} + ‖v‖_{H^m(B_R)})`
(`lem:local-div-curl`). The field `V = χv` is compactly supported with
`div V = ∇χ · v` and `curl V = χζ + ∇χ × v`, both in `H^m(ℝ³)`, so the
whole-space estimate for compactly supported fields applies. Since `χ = 1` on
`B_r`, the resulting family restricts to one of `v` on `B_r`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem wordDeriv_translate (γ : List (Fin 3)) (g : Vec3 → ℝ) (x₀ : Vec3) :
    wordDeriv γ (fun x => g (x - x₀)) = fun x => wordDeriv γ g (x - x₀) := by
  induction γ generalizing g with
  | nil => rfl
  | cons j γ ih =>
      have h : spatialDeriv (fun x => g (x - x₀)) j = fun x => spatialDeriv g j (x - x₀) :=
        funext fun x => vorticitySpatialDeriv_translate g x₀ x j
      change wordDeriv γ (spatialDeriv (fun x => g (x - x₀)) j) = _
      rw [h]
      exact ih (spatialDeriv g j)

theorem tsupport_wordDeriv_subset (γ : List (Fin 3)) (g : Vec3 → ℝ) :
    tsupport (wordDeriv γ g) ⊆ tsupport g := by
  induction γ generalizing g with
  | nil => exact subset_rfl
  | cons j γ ih =>
      exact (ih (spatialDeriv g j)).trans (tsupport_fderiv_apply_subset ℝ (basisVec j))

theorem sobolevNormSqOn_add_le {m : ℕ} {W : Set Vec3} {A B : List (Fin 3) → Vec3 → ℝ}
    (hA : ∀ α ∈ sobolevWords m, MemLp (A α) 2 (volume.restrict W))
    (hB : ∀ α ∈ sobolevWords m, MemLp (B α) 2 (volume.restrict W)) :
    sobolevNormSqOn m W (fun α x => A α x + B α x) ≤
      2 * sobolevNormSqOn m W A + 2 * sobolevNormSqOn m W B := by
  unfold sobolevNormSqOn
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun α hα => ?_
  have iA := (hA α hα).integrable_sq
  have iB := (hB α hα).integrable_sq
  have iAB := ((hA α hα).add (hB α hα)).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul 2)
    (iB.const_mul 2)]
  refine integral_mono iAB ((iA.const_mul 2).add (iB.const_mul 2)) fun x => ?_
  nlinarith only [sq_nonneg (A α x - B α x)]

theorem sobolevNormSqOn_neg {m : ℕ} {W : Set Vec3} (A : List (Fin 3) → Vec3 → ℝ) :
    sobolevNormSqOn m W (fun α x => (-1) * A α x) = sobolevNormSqOn m W A := by
  unfold sobolevNormSqOn
  refine Finset.sum_congr rfl fun α _ => integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring

theorem sobolevNormSqOn_mono_set {m : ℕ} {W₁ W₂ : Set Vec3} (h : W₁ ⊆ W₂)
    {A : List (Fin 3) → Vec3 → ℝ} (hA : ∀ α ∈ sobolevWords m, MemLp (A α) 2 (volume.restrict W₂)) :
    sobolevNormSqOn m W₁ A ≤ sobolevNormSqOn m W₂ A :=
  Finset.sum_le_sum fun α hα => setIntegral_mono_set (hA α hα).integrable_sq
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ h)

/-- Finite sums of Sobolev families. -/
theorem _root_.CKN.IsSobolevFamilyOn.finset_sum {ι : Type*} (s : Finset ι) {m : ℕ} {U : Set Vec3}
    {f : ι → Vec3 → ℝ} {D : ι → List (Fin 3) → Vec3 → ℝ}
    (h : ∀ i ∈ s, IsSobolevFamilyOn m U (f i) (D i)) :
    IsSobolevFamilyOn m U (fun x => ∑ i ∈ s, f i x) (fun α x => ∑ i ∈ s, D i α x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Filter.EventuallyEq.rfl, fun _ _ => by simp, ?_⟩
      intro α j _ φ _ _ _
      simp
  | insert i s hi ih =>
      have h1 := h i (Finset.mem_insert_self i s)
      have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      have h3 := h1.add h2
      refine h3.congr_ae (ae_of_all _ fun x => ?_) fun α _ => ae_of_all _ fun x => ?_
      · simp [Finset.sum_insert hi]
      · simp [Finset.sum_insert hi]

/-- The local div–curl estimate, given the whole-space estimate for compactly
supported fields. -/
theorem localDivCurl_of_whole (m : ℕ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hW : ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Fin 3 → Vec3 → ℝ) (DV : Fin 3 → List (Fin 3) → Vec3 → ℝ)
      (d : Vec3 → ℝ) (Dd : List (Fin 3) → Vec3 → ℝ)
      (ω : Fin 3 → Vec3 → ℝ) (Dω : Fin 3 → List (Fin 3) → Vec3 → ℝ) (K : Set Vec3),
      IsCompact K → (∀ i x, x ∉ K → V i x = 0) →
      (∀ i, IsSobolevFamilyOn m univ (V i) (DV i)) →
      IsSobolevFamilyOn m univ d Dd →
      (∀ k, IsSobolevFamilyOn m univ (ω k) (Dω k)) →
      (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, ∑ i : Fin 3, V i x * spatialDeriv φ i x = -∫ x, d x * φ x) →
      (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ k : Fin 3,
        ∫ x, ω k x * φ x =
          ∫ x, (V (k + 1) x * spatialDeriv φ (k + 2) x -
            V (k + 2) x * spatialDeriv φ (k + 1) x)) →
      ∃ DV' : Fin 3 → List (Fin 3) → Vec3 → ℝ,
        (∀ i, IsSobolevFamilyOn (m + 1) univ (V i) (DV' i)) ∧
        ∑ i, sobolevNormSqOn (m + 1) univ (DV' i) ≤
          C * (sobolevNormSqOn m univ Dd + ∑ k, sobolevNormSqOn m univ (Dω k) +
            ∑ i, sobolevNormSqOn m univ (DV i))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (v ζ : Vec3 → Vec3),
      hNormOn m (vec3Ball x₀ R) (vecComponents v) < ⊤ →
      hNormOn m (vec3Ball x₀ R) (vecComponents ζ) < ⊤ →
      IsWeakDivCurlOn (vec3Ball x₀ R) v ζ →
      hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents v) ≤
        ENNReal.ofReal C * (hNormOn m (vec3Ball x₀ R) (vecComponents ζ) +
          hNormOn m (vec3Ball x₀ R) (vecComponents v)) := by
  set R₁ : ℝ := (r + R) / 2 with hR₁
  have hrR₁ : r < R₁ := by rw [hR₁]; linarith only [hrR]
  have hR₁R : R₁ < R := by rw [hR₁]; linarith only [hrR]
  obtain ⟨χ₀, hχ₀, hχ₀c, hχ₀supp, hχ₀one, -, -⟩ := vorticitySpatialCutoff_exists hr hrR₁
  have hbd (γ : List (Fin 3)) : ∃ Lγ : ℝ, ∀ y, |wordDeriv γ χ₀ y| ≤ Lγ := by
    have hc : HasCompactSupport (wordDeriv γ χ₀) :=
      hχ₀c.mono' ((subset_tsupport _).trans (tsupport_wordDeriv_subset γ χ₀))
    obtain ⟨M, hM⟩ := (contDiff_wordDeriv hχ₀ γ).continuous.bounded_above_of_compact_support hc
    exact ⟨M, fun y => by simpa only [Real.norm_eq_abs] using hM y⟩
  choose Lf hLf using hbd
  set L : ℝ := ∑ γ ∈ sobolevWords (m + 1), |Lf γ| with hLdef
  have hL : ∀ γ : List (Fin 3), γ.length ≤ m + 1 → ∀ y, |wordDeriv γ χ₀ y| ≤ L :=
    fun γ hγ y => (hLf γ y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun γ => |Lf γ|) (fun _ _ => abs_nonneg _)
        (mem_sobolevWords.2 hγ)))
  obtain ⟨CW, hCW, hWf⟩ := hW
  obtain ⟨CL, hCL, hLeib⟩ := sobolevLeibnizFamily_normSq_le m
  set K₂ : ℝ := 17 * (CL * L ^ 2) with hK₂
  have hCLL : 0 ≤ CL * L ^ 2 := mul_nonneg hCL (sq_nonneg L)
  refine ⟨Real.sqrt (CW * K₂), Real.sqrt_nonneg _, ?_⟩
  intro x₀ v ζ hv hζ hdc
  set U : Set Vec3 := vec3Ball x₀ R with hU
  have hUo : IsOpen U := isOpen_vec3Ball x₀ R
  choose Dv hDv using hNormOn_lt_top_iff.1 hv
  choose Dζ hDζ using hNormOn_lt_top_iff.1 hζ
  -- the cutoff
  let χ : Vec3 → ℝ := fun x => χ₀ (x - x₀)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hχ₀.comp (contDiff_id.sub contDiff_const)
  have hχc : HasCompactSupport χ := hχ₀c.comp_homeomorph (Homeomorph.subRight x₀)
  set T : Set Vec3 := tsupport χ with hT
  have hTc : IsClosed T := isClosed_tsupport χ
  have hTU : T ⊆ U := by
    have hsupp : Function.support χ ⊆ (fun x => x - x₀) ⁻¹' tsupport χ₀ :=
      fun x hx => subset_tsupport χ₀ hx
    refine (closure_minimal hsupp ((isClosed_tsupport χ₀).preimage
      (continuous_id.sub continuous_const))).trans fun x hx => ?_
    have h := hχ₀supp hx
    change vec3EuclideanNorm (x - x₀ - 0) < R₁ at h
    rw [sub_zero] at h
    exact lt_trans h hR₁R
  have hwχ (γ : List (Fin 3)) (y : Vec3) : wordDeriv γ χ y = wordDeriv γ χ₀ (y - x₀) :=
    congrFun (wordDeriv_translate γ χ₀ x₀) y
  have hχb (α : List (Fin 3)) (hα : α.length ≤ m) (y : Vec3) : |wordDeriv α χ y| ≤ L := by
    rw [hwχ]; exact hL α (by omega) _
  have hχ0 (α : List (Fin 3)) (y : Vec3) (hy : y ∉ T) : wordDeriv α χ y = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_wordDeriv_subset α χ h)
  -- the gradient multipliers
  let g : Fin 3 → Vec3 → ℝ := fun i => spatialDeriv χ i
  have hg (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g i) := contDiff_spatialDeriv_smooth hχ i
  have hgc (i : Fin 3) : HasCompactSupport (g i) := hχc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hgU (i : Fin 3) : tsupport (g i) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hTU
  have hgb (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m) (y : Vec3) :
      |wordDeriv α (g i) y| ≤ L := by
    change |wordDeriv (i :: α) χ y| ≤ L
    rw [hwχ]; exact hL _ (by simp only [List.length_cons]; omega) _
  have hg0 (i : Fin 3) (α : List (Fin 3)) (y : Vec3) (hy : y ∉ T) : wordDeriv α (g i) y = 0 :=
    hχ0 (i :: α) y hy
  -- families of the cutoff data
  have hVf (i : Fin 3) := (hDv i).smooth_mul_univ hUo hχ hχc hTU
  have hgf (i j : Fin 3) := (hDv j).smooth_mul_univ hUo (hg i) (hgc i) (hgU i)
  have hdf := CKN.IsSobolevFamilyOn.finset_sum Finset.univ fun i _ => hgf i i
  have hωf (k : Fin 3) := ((hDζ k).smooth_mul_univ hUo hχ hχc hTU).add
    ((hgf (k + 1) (k + 2)).add ((hgf (k + 2) (k + 1)).const_mul (-1)))
  -- square integrability of the data
  have hvL (i : Fin 3) : MemLp (fun x => v x i) 2 (volume.restrict U) :=
    ((hDv i).memL2 [] (Nat.zero_le _)).ae_eq (hDv i).zero
  have hζL (k : Fin 3) : MemLp (fun x => ζ x k) 2 (volume.restrict U) :=
    ((hDζ k).memL2 [] (Nat.zero_le _)).ae_eq (hDζ k).zero
  -- the explicit families
  let Lb : (Vec3 → ℝ) → (List (Fin 3) → Vec3 → ℝ) → List (Fin 3) → Vec3 → ℝ :=
    fun h B α => sobolevLeibnizFamily α (fun β => wordDeriv β h) B
  let DVf : Fin 3 → List (Fin 3) → Vec3 → ℝ := fun i => Lb χ (Dv i)
  let Ddf : List (Fin 3) → Vec3 → ℝ := fun α x => ∑ i ∈ Finset.univ, Lb (g i) (Dv i) α x
  let Dωf : Fin 3 → List (Fin 3) → Vec3 → ℝ := fun k α x =>
    Lb χ (Dζ k) α x + (Lb (g (k + 1)) (Dv (k + 2)) α x + (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x)
  obtain ⟨DV', hfam', hbnd⟩ := hWf (fun i x => χ x * v x i) DVf
    (fun x => ∑ i ∈ Finset.univ, g i x * vecComponents v i x) Ddf
    (fun k x => χ x * vecComponents ζ k x + (g (k + 1) x * vecComponents v (k + 2) x +
      (-1) * (g (k + 2) x * vecComponents v (k + 1) x))) Dωf T
    hχc.isCompact (fun i x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    hVf hdf hωf
    (fun φ hφ _ => cutoff_weakDiv hχ hχc hTU hvL hdc.1 φ hφ)
    (fun φ hφ _ k => by
      rw [← cutoff_weakCurl hχ hχc hTU hvL hζL hdc.2 φ hφ k]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [g, vecComponents]
      ring)
  -- restriction to `B_r`
  have hvr (i : Fin 3) :
      IsSobolevFamilyOn (m + 1) (vec3Ball x₀ r) (vecComponents v i) (DV' i) := by
    refine ((hfam' i).mono_set (isOpen_vec3Ball x₀ r) (subset_univ _)).congr_ae ?_
      (fun α _ => Filter.EventuallyEq.rfl)
    refine (ae_restrict_iff' (isOpen_vec3Ball x₀ r).measurableSet).2
      (ae_of_all _ fun x hx => ?_)
    have h1 : χ x = 1 := hχ₀one (x - x₀) (le_of_lt hx)
    simp only [vecComponents, h1, one_mul]
  -- the norm bounds of the data
  set P : ℝ := ∑ i, sobolevNormSqOn m U (Dv i) with hP
  set Q : ℝ := ∑ k, sobolevNormSqOn m U (Dζ k) with hQ
  have hPi0 (i : Fin 3) : 0 ≤ sobolevNormSqOn m U (Dv i) :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hQk0 (k : Fin 3) : 0 ≤ sobolevNormSqOn m U (Dζ k) :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => hPi0 i
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => hQk0 k
  have hbV (i : Fin 3) : sobolevNormSqOn m univ (DVf i) ≤ CL * L ^ 2 * sobolevNormSqOn m U (Dv i) :=
    vorticityProducts_leibniz_univ_normSq_le hLeib hCL hUo hTc hTU hχ hχb hχ0 (hDv i)
  have hbg (i j : Fin 3) : sobolevNormSqOn m univ (Lb (g i) (Dv j)) ≤
      CL * L ^ 2 * sobolevNormSqOn m U (Dv j) :=
    vorticityProducts_leibniz_univ_normSq_le hLeib hCL hUo hTc hTU (hg i) (hgb i) (hg0 i) (hDv j)
  have hbζ (k : Fin 3) : sobolevNormSqOn m univ (Lb χ (Dζ k)) ≤
      CL * L ^ 2 * sobolevNormSqOn m U (Dζ k) :=
    vorticityProducts_leibniz_univ_normSq_le hLeib hCL hUo hTc hTU hχ hχb hχ0 (hDζ k)
  have hLg (i j : Fin 3) : ∀ α ∈ sobolevWords m, MemLp (Lb (g i) (Dv j) α) 2 (volume.restrict univ) :=
    fun α hα => (hgf i j).memL2 α (mem_sobolevWords.1 hα)
  have hLζ (k : Fin 3) : ∀ α ∈ sobolevWords m, MemLp (Lb χ (Dζ k) α) 2 (volume.restrict univ) :=
    fun α hα => ((hDζ k).smooth_mul_univ hUo hχ hχc hTU).memL2 α (mem_sobolevWords.1 hα)
  -- the divergence
  have hbd : sobolevNormSqOn m univ Ddf ≤ 4 * (CL * L ^ 2) * P := by
    have e : Ddf = fun α x => (Lb (g 0) (Dv 0) α x + Lb (g 1) (Dv 1) α x) + Lb (g 2) (Dv 2) α x := by
      funext α x
      simp only [Ddf, Fin.sum_univ_three]
    rw [e]
    have h01 : sobolevNormSqOn m univ (fun α x => Lb (g 0) (Dv 0) α x + Lb (g 1) (Dv 1) α x) ≤
        2 * sobolevNormSqOn m univ (Lb (g 0) (Dv 0)) +
          2 * sobolevNormSqOn m univ (Lb (g 1) (Dv 1)) :=
      sobolevNormSqOn_add_le (hLg 0 0) (hLg 1 1)
    have h012 : sobolevNormSqOn m univ (fun α x =>
        (Lb (g 0) (Dv 0) α x + Lb (g 1) (Dv 1) α x) + Lb (g 2) (Dv 2) α x) ≤
        2 * sobolevNormSqOn m univ (fun α x => Lb (g 0) (Dv 0) α x + Lb (g 1) (Dv 1) α x) +
          2 * sobolevNormSqOn m univ (Lb (g 2) (Dv 2)) :=
      sobolevNormSqOn_add_le (fun α hα => (hLg 0 0 α hα).add (hLg 1 1 α hα)) (hLg 2 2)
    have hPe : P = sobolevNormSqOn m U (Dv 0) + sobolevNormSqOn m U (Dv 1) +
        sobolevNormSqOn m U (Dv 2) := by rw [hP, Fin.sum_univ_three]
    rw [hPe]
    linarith only [h01, h012, hbg 0 0, hbg 1 1, hbg 2 2, hCLL, hPi0 0, hPi0 1, hPi0 2,
      mul_nonneg hCLL (hPi0 0), mul_nonneg hCLL (hPi0 1), mul_nonneg hCLL (hPi0 2)]
  -- the curls
  have hbω (k : Fin 3) : sobolevNormSqOn m univ (Dωf k) ≤
      2 * (CL * L ^ 2) * sobolevNormSqOn m U (Dζ k) +
        4 * (CL * L ^ 2) * (sobolevNormSqOn m U (Dv (k + 2)) +
          sobolevNormSqOn m U (Dv (k + 1))) := by
    have h1 : sobolevNormSqOn m univ (fun α x => Lb χ (Dζ k) α x +
        (Lb (g (k + 1)) (Dv (k + 2)) α x + (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x)) ≤
        2 * sobolevNormSqOn m univ (Lb χ (Dζ k)) +
          2 * sobolevNormSqOn m univ (fun α x => Lb (g (k + 1)) (Dv (k + 2)) α x +
            (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x) :=
      sobolevNormSqOn_add_le (hLζ k) (fun α hα =>
        (hLg (k + 1) (k + 2) α hα).add ((hLg (k + 2) (k + 1) α hα).const_mul (-1)))
    have h2 : sobolevNormSqOn m univ (fun α x => Lb (g (k + 1)) (Dv (k + 2)) α x +
        (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x) ≤
        2 * sobolevNormSqOn m univ (Lb (g (k + 1)) (Dv (k + 2))) +
          2 * sobolevNormSqOn m univ (fun α x => (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x) :=
      sobolevNormSqOn_add_le (hLg (k + 1) (k + 2))
        (fun α hα => (hLg (k + 2) (k + 1) α hα).const_mul (-1))
    have h3 : sobolevNormSqOn m univ (fun α x => (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x) =
        sobolevNormSqOn m univ (Lb (g (k + 2)) (Dv (k + 1))) := sobolevNormSqOn_neg _
    change sobolevNormSqOn m univ (fun α x => Lb χ (Dζ k) α x +
      (Lb (g (k + 1)) (Dv (k + 2)) α x + (-1) * Lb (g (k + 2)) (Dv (k + 1)) α x)) ≤ _
    have hb1 := hbζ k
    have hb2 := hbg (k + 1) (k + 2)
    have hb3 := hbg (k + 2) (k + 1)
    nlinarith only [h1, h2, h3, hb1, hb2, hb3]
  have hsumω : ∑ k, sobolevNormSqOn m univ (Dωf k) ≤ 2 * (CL * L ^ 2) * Q + 8 * (CL * L ^ 2) * P := by
    refine (Finset.sum_le_sum fun k _ => hbω k).trans (le_of_eq ?_)
    rw [hP, hQ]
    simp only [Fin.sum_univ_three, Fin.isValue]
    norm_num
    ring
  have hsumV : ∑ i, sobolevNormSqOn m univ (DVf i) ≤ (CL * L ^ 2) * P := by
    rw [hP, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hbV i
  -- conclusion
  have hr_le : ∑ i, sobolevNormSqOn (m + 1) (vec3Ball x₀ r) (DV' i) ≤ CW * K₂ * (P + Q) := by
    have hmono : ∑ i, sobolevNormSqOn (m + 1) (vec3Ball x₀ r) (DV' i) ≤
        ∑ i, sobolevNormSqOn (m + 1) univ (DV' i) :=
      Finset.sum_le_sum fun i _ => sobolevNormSqOn_mono_set (subset_univ _)
        fun α hα => (hfam' i).memL2 α (mem_sobolevWords.1 hα)
    have hsum := add_le_add (add_le_add hbd hsumω) hsumV
    have hK : sobolevNormSqOn m univ Ddf + ∑ k, sobolevNormSqOn m univ (Dωf k) +
        ∑ i, sobolevNormSqOn m univ (DVf i) ≤ K₂ * (P + Q) := by
      rw [hK₂]
      nlinarith only [hsum, mul_nonneg hCLL hP0, mul_nonneg hCLL hQ0]
    calc
      _ ≤ _ := hmono
      _ ≤ _ := hbnd
      _ ≤ CW * (K₂ * (P + Q)) := mul_le_mul_of_nonneg_left hK hCW
      _ = CW * K₂ * (P + Q) := by ring
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  rw [hNormOn_eq hUo hDζ, hNormOn_eq hUo hDv]
  refine (hNormOn_le hvr).trans ?_
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc
    Real.sqrt (∑ i, sobolevNormSqOn (m + 1) (vec3Ball x₀ r) (DV' i)) ≤
        Real.sqrt (CW * K₂ * (P + Q)) := Real.sqrt_le_sqrt hr_le
    _ = Real.sqrt (CW * K₂) * Real.sqrt (P + Q) := Real.sqrt_mul (mul_nonneg hCW hK₂0) _
    _ ≤ Real.sqrt (CW * K₂) * (Real.sqrt Q + Real.sqrt P) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      rw [add_comm (Real.sqrt Q)]
      exact real_sqrt_add_le_add_sqrt hP0 hQ0

/-- The time-integrated and time-supremum forms of a pointwise estimate. -/
theorem localDivCurl_time_of_pointwise (m : ℕ) {r R C : ℝ}
    (h : ∀ (x₀ : Vec3) (v ζ : Vec3 → Vec3),
      hNormOn m (vec3Ball x₀ R) (vecComponents v) < ⊤ →
      hNormOn m (vec3Ball x₀ R) (vecComponents ζ) < ⊤ →
      IsWeakDivCurlOn (vec3Ball x₀ R) v ζ →
      hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents v) ≤
        ENNReal.ofReal C * (hNormOn m (vec3Ball x₀ R) (vecComponents ζ) +
          hNormOn m (vec3Ball x₀ R) (vecComponents v))) :
    ∀ (x₀ : Vec3) (I : Set ℝ) (v ζ : ℝ → Vec3 → Vec3),
      (∀ᵐ t ∂(volume.restrict I),
        hNormOn m (vec3Ball x₀ R) (vecComponents (v t)) < ⊤ ∧
        hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) < ⊤ ∧
        IsWeakDivCurlOn (vec3Ball x₀ R) (v t) (ζ t)) →
      (∫⁻ t in I, hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents (v t)) ^ 2) ≤
          ENNReal.ofReal C ^ 2 * ∫⁻ t in I,
            (hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) +
              hNormOn m (vec3Ball x₀ R) (vecComponents (v t))) ^ 2 ∧
      essSup (fun t => hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents (v t)))
          (volume.restrict I) ≤
        ENNReal.ofReal C * essSup (fun t =>
          hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) +
            hNormOn m (vec3Ball x₀ R) (vecComponents (v t))) (volume.restrict I) := by
  intro x₀ I v ζ hae
  have hpt : ∀ᵐ t ∂(volume.restrict I),
      hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents (v t)) ≤
        ENNReal.ofReal C * (hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) +
          hNormOn m (vec3Ball x₀ R) (vecComponents (v t))) := by
    filter_upwards [hae] with t ht
    exact h x₀ (v t) (ζ t) ht.1 ht.2.1 ht.2.2
  refine ⟨?_, ?_⟩
  · rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with t ht
    rw [← mul_pow]
    exact pow_le_pow_left' ht 2
  · rw [← ENNReal.essSup_const_mul]
    exact essSup_mono_ae hpt

end ESS
