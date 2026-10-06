/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainBounds

/-!
# The space-time cutoffs of `lem:local-heat-gain`

For concentric balls `B_r ⋐ B_R` and a time gap `σ > 0`, the separated cutoff
`η(x, t) = θ(t - a) χ(x - x₀)` equals one on `B_r × [a + σ, ∞)`, vanishes for
`t < a + σ/2` and for `x` outside a compact subset of `B_R`, and its spatial
derivatives, those of `∂ₜη - Δη` and those of `∇η` are bounded through any
fixed order by a constant independent of the center `x₀` and of `a`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Word derivatives vanish on an open set where the function vanishes. -/
theorem wordDeriv_eq_zero_of_eqOn {W : Set Vec3} (hW : IsOpen W) {g : Vec3 → ℝ}
    (hg : ∀ y ∈ W, g y = 0) (γ : List (Fin 3)) : ∀ y ∈ W, wordDeriv γ g y = 0 := by
  induction γ generalizing g with
  | nil => exact hg
  | cons j γ ih =>
      apply ih
      intro y hy
      have hev : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hW.mem_nhds hy] with z hz
        exact hg z hz
      change (fderiv ℝ g y) (basisVec j) = 0
      rw [hev.fderiv_eq]
      simp

/-- Word derivatives of positive length vanish on an open set where the
function is constant one. -/
theorem wordDeriv_eq_zero_of_eqOn_one {W : Set Vec3} (hW : IsOpen W) {g : Vec3 → ℝ}
    (hg : ∀ y ∈ W, g y = 1) (γ : List (Fin 3)) (hγ : γ ≠ []) :
    ∀ y ∈ W, wordDeriv γ g y = 0 := by
  obtain ⟨j, γ', rfl⟩ := List.exists_cons_of_ne_nil hγ
  refine wordDeriv_eq_zero_of_eqOn hW (fun y hy => ?_) γ'
  have hev : g =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [hW.mem_nhds hy] with z hz
    exact hg z hz
  change (fderiv ℝ g y) (basisVec j) = 0
  rw [hev.fderiv_eq]
  simp

theorem mem_vec3Ball_iff_sub {x₀ y : Vec3} {R : ℝ} :
    y ∈ vec3Ball x₀ R ↔ y - x₀ ∈ vec3Ball 0 R := by
  show vec3EuclideanNorm (y - x₀) < R ↔ vec3EuclideanNorm (y - x₀ - 0) < R
  rw [sub_zero]

/-- The cutoffs of `lem:local-heat-gain`. -/
theorem localHeatGain_cutoffs (m : ℕ) {r R σ : ℝ} (hr : 0 < r) (hrR : r < R) (hσ : 0 < σ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x₀ : Vec3) (a : ℝ), ∃ (η : Vec3 × ℝ → ℝ) (K N : Set Vec3)
      (κ : Vec3 → ℝ),
      IsLocalHeatCutoff (vec3Ball x₀ R) K η ∧ IsOpen N ∧ K ⊆ N ∧
      ContDiff ℝ (⊤ : ℕ∞) κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ vec3Ball x₀ R ∧
      (∀ x ∈ N, κ x = 1) ∧
      (∀ γ : List (Fin 3), γ.length ≤ m → ∀ p, |spaceTimeWord γ η p| ≤ L) ∧
      (∀ γ : List (Fin 3), γ.length ≤ m → ∀ p,
        |spaceTimeWord γ (localHeatGainZeta η) p| ≤ L) ∧
      (∀ (j : Fin 3) (γ : List (Fin 3)), γ.length ≤ m → ∀ p,
        |spaceTimeWord γ (fun q => spatialPartial η j q) p| ≤ L) ∧
      (∀ (γ : List (Fin 3)) (p : Vec3 × ℝ), p.2 ≤ a + σ / 2 → spaceTimeWord γ η p = 0) ∧
      (∀ p : Vec3 × ℝ, p.1 ∈ vec3Ball x₀ r → a + σ ≤ p.2 →
        spaceTimeWord [] η p = 1 ∧ ∀ γ : List (Fin 3), γ ≠ [] → spaceTimeWord γ η p = 0) := by
  -- radii
  set r₂ : ℝ := r + (R - r) / 4 with hr₂
  set R₂ : ℝ := r + (R - r) / 2 with hR₂
  set R₃ : ℝ := r + 3 * (R - r) / 4 with hR₃
  have h0r₂ : 0 < r₂ := by rw [hr₂]; linarith only [hr, hrR]
  have hrr₂ : r < r₂ := by rw [hr₂]; linarith only [hrR]
  have hr₂R₂ : r₂ < R₂ := by rw [hr₂, hR₂]; linarith only [hrR]
  have hR₂R₃ : R₂ < R₃ := by rw [hR₂, hR₃]; linarith only [hrR]
  have h0R₃ : 0 < R₃ := by rw [hR₃]; linarith only [hr, hrR]
  have hR₃R : R₃ < R := by rw [hR₃]; linarith only [hrR]
  obtain ⟨χ₀, hχ₀, hχ₀c, hχ₀supp, hχ₀one, -, -⟩ := vorticitySpatialCutoff_exists h0r₂ hr₂R₂
  obtain ⟨κ₀, hκ₀, hκ₀c, hκ₀supp, hκ₀one, -, -⟩ := vorticitySpatialCutoff_exists h0R₃ hR₃R
  obtain ⟨θ₀, hθ₀, hθ₀0, hθ₀1, hθ₀nn, hθ₀le, Lθ, hLθ0, hLθ⟩ := vorticityTimeCutoff_exists hσ
  -- per-word bounds, uniform in the center and in the time shift
  have hbη (γ : List (Fin 3)) := spaceTimeWord_separated_bound hχ₀ hχ₀c 1 γ
  have hbt (γ : List (Fin 3)) := spaceTimeWord_separated_bound hχ₀ hχ₀c Lθ γ
  have hχkk (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (wordDeriv [k, k] χ₀) :=
    contDiff_wordDeriv_of_contDiff hχ₀ _
  have hbkk (k : Fin 3) (γ : List (Fin 3)) := spaceTimeWord_separated_bound (hχkk k)
    (hasCompactSupport_wordDeriv hχ₀c [k, k]) 1 γ
  have hbg (j : Fin 3) (γ : List (Fin 3)) := spaceTimeWord_separated_bound
    (contDiff_spatialDeriv_smooth hχ₀ j) (hχ₀c.fderiv_apply (𝕜 := ℝ) (basisVec j)) 1 γ
  choose Lη hLη using hbη
  choose Lt hLt using hbt
  choose Lkk hLkk using hbkk
  choose Lg hLg using hbg
  let L : ℝ := ∑ γ ∈ sobolevWords m, (|Lη γ| + |Lt γ| + ∑ k : Fin 3, |Lkk k γ| +
    ∑ j : Fin 3, |Lg j γ|)
  have hLterm (γ : List (Fin 3)) (hγ : γ.length ≤ m) :
      |Lη γ| + |Lt γ| + ∑ k : Fin 3, |Lkk k γ| + ∑ j : Fin 3, |Lg j γ| ≤ L :=
    Finset.single_le_sum (f := fun γ => |Lη γ| + |Lt γ| + ∑ k : Fin 3, |Lkk k γ| +
      ∑ j : Fin 3, |Lg j γ|) (fun γ _ => by positivity) (mem_sobolevWords.2 hγ)
  have hS (γ : List (Fin 3)) : 0 ≤ ∑ k : Fin 3, |Lkk k γ| := by positivity
  have hS' (γ : List (Fin 3)) : 0 ≤ ∑ j : Fin 3, |Lg j γ| := by positivity
  refine ⟨L, Finset.sum_nonneg fun γ _ => by positivity, ?_⟩
  intro x₀ a
  -- the cutoff
  let c : ℝ → ℝ := fun t => θ₀ (t - a)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := hθ₀.comp (contDiff_id.sub contDiff_const)
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hcb : ∀ t, |c t| ≤ 1 := fun t => by
    rw [abs_le]; exact ⟨by linarith only [hθ₀nn (t - a)], hθ₀le _⟩
  have hdc : ∀ t, deriv c t = deriv θ₀ (t - a) := fun t =>
    deriv_comp_sub_const (f := θ₀) (a := a) (x := t)
  have hdcb : ∀ t, |deriv c t| ≤ Lθ := fun t => by rw [hdc]; exact hLθ _
  let η : Vec3 × ℝ → ℝ := fun q => c q.2 * χ₀ (q.1 - x₀)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    (hc.comp contDiff_snd).mul (hχ₀.comp (contDiff_fst.sub contDiff_const))
  -- the time derivative and the Laplacian in separated form
  have ht : (fun q : Vec3 × ℝ => timePartial η q) =
      fun q => deriv c q.2 * χ₀ (q.1 - x₀) :=
    funext fun q => timePartial_separated hcd χ₀ x₀ q
  have hkk (k : Fin 3) : (fun q : Vec3 × ℝ => spatialSecondPartial η k k q) =
      fun q => c q.2 * wordDeriv [k, k] χ₀ (q.1 - x₀) :=
    spaceTimeWord_separated [k, k] c hχ₀ x₀
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => timePartial η q) :=
    vorticityHeatSmooth_timePartial_contDiff hη
  have hB (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialSecondPartial η k k q) :=
    vorticityHeatSmooth_spatialPartial_contDiff (vorticityHeatSmooth_spatialPartial_contDiff hη k) k
  have hζword (γ : List (Fin 3)) (p : Vec3 × ℝ) :
      |spaceTimeWord γ (localHeatGainZeta η) p| ≤ |Lt γ| + ∑ k : Fin 3, |Lkk k γ| := by
    have h := congrFun (spaceTimeWord_sub_sum γ hA hB) p
    change spaceTimeWord γ (localHeatGainZeta η) p = _ at h
    rw [h]
    have h1 : |spaceTimeWord γ (fun q : Vec3 × ℝ => timePartial η q) p| ≤ |Lt γ| := by
      rw [ht]
      exact (hLt γ x₀ (deriv c) hdcb p).trans (le_abs_self _)
    have h2 (k : Fin 3) :
        |spaceTimeWord γ (fun q : Vec3 × ℝ => spatialSecondPartial η k k q) p| ≤ |Lkk k γ| := by
      rw [hkk k]
      exact (hLkk k γ x₀ c hcb p).trans (le_abs_self _)
    calc
      _ ≤ |spaceTimeWord γ (fun q : Vec3 × ℝ => timePartial η q) p| +
          |∑ k : Fin 3, spaceTimeWord γ (fun q : Vec3 × ℝ => spatialSecondPartial η k k q) p| :=
        abs_sub _ _
      _ ≤ |Lt γ| + ∑ k : Fin 3, |Lkk k γ| :=
        add_le_add h1 ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => h2 k))
  have hgrad (j : Fin 3) : (fun q : Vec3 × ℝ => spatialPartial η j q) =
      fun q => c q.2 * spatialDeriv χ₀ j (q.1 - x₀) :=
    funext fun q => spatialPartial_separated (hχ₀.differentiable (by simp)) x₀ j q
  have hgword (j : Fin 3) (γ : List (Fin 3)) (p : Vec3 × ℝ) :
      |spaceTimeWord γ (fun q => spatialPartial η j q) p| ≤ |Lg j γ| := by
    rw [hgrad j]
    exact (hLg j γ x₀ c hcb p).trans (le_abs_self _)
  -- the supports
  let K : Set Vec3 := (fun y => y + x₀) '' tsupport χ₀
  have hK : IsCompact K := hχ₀c.isCompact.image (continuous_id.add continuous_const)
  have hKR₂ : K ⊆ vec3Ball x₀ R₂ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_vec3Ball_iff_sub, add_sub_cancel_right]
    exact hχ₀supp hy
  have hball_mono {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) : vec3Ball x₀ ρ₁ ⊆ vec3Ball x₀ ρ₂ :=
    fun y hy => lt_of_lt_of_le hy h
  have hηK : ∀ x, x ∉ K → ∀ t, η (x, t) = 0 := by
    intro x hx t
    have hx' : x - x₀ ∉ tsupport χ₀ := fun h => hx ⟨x - x₀, h, sub_add_cancel x x₀⟩
    simp [η, image_eq_zero_of_notMem_tsupport hx']
  let κ : Vec3 → ℝ := fun x => κ₀ (x - x₀)
  have hκc : HasCompactSupport κ := hκ₀c.comp_homeomorph (Homeomorph.subRight x₀)
  have hκR : tsupport κ ⊆ vec3Ball x₀ R := by
    have hsupp : Function.support κ ⊆ (fun x => x - x₀) ⁻¹' tsupport κ₀ :=
      fun x hx => subset_tsupport κ₀ hx
    refine (closure_minimal hsupp ((isClosed_tsupport κ₀).preimage
      (continuous_id.sub continuous_const))).trans fun x hx => ?_
    rw [mem_vec3Ball_iff_sub]
    exact hκ₀supp hx
  refine ⟨η, K, vec3Ball x₀ R₃, κ,
    ⟨hη, hK, hKR₂.trans (hball_mono (by linarith only [hR₂R₃, hR₃R])), hηK,
      fun γ => ⟨Lη γ, hLη γ x₀ c hcb⟩, fun γ => ⟨_, hζword γ⟩, fun j γ => ⟨_, hgword j γ⟩⟩,
    isOpen_vec3Ball x₀ R₃, hKR₂.trans (hball_mono hR₂R₃.le),
    hκ₀.comp (contDiff_id.sub contDiff_const), hκc, hκR,
    fun x hx => hκ₀one (x - x₀) (le_of_lt (by simpa [vec3Ball] using hx)),
    fun γ hγ p => ?_, fun γ hγ p => ?_, fun j γ hγ p => ?_, fun γ p hp => ?_, fun p hp1 hp2 => ?_⟩
  · have h := hLterm γ hγ
    have h2 : |Lη γ| ≤ L := by
      linarith only [h, hS γ, hS' γ, abs_nonneg (Lt γ)]
    exact (hLη γ x₀ c hcb p).trans ((le_abs_self _).trans h2)
  · have h := hLterm γ hγ
    have h2 : |Lt γ| + ∑ k : Fin 3, |Lkk k γ| ≤ L := by
      linarith only [h, hS' γ, abs_nonneg (Lη γ)]
    exact (hζword γ p).trans h2
  · have h := hLterm γ hγ
    have hj : |Lg j γ| ≤ ∑ j : Fin 3, |Lg j γ| :=
      Finset.single_le_sum (f := fun j => |Lg j γ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : |Lg j γ| ≤ L := by
      linarith only [h, hj, hS γ, abs_nonneg (Lη γ), abs_nonneg (Lt γ)]
    exact (hgword j γ p).trans h2
  · rw [spaceTimeWord_separated γ c hχ₀ x₀]
    simp only [c, hθ₀0 (p.2 - a) (by linarith only [hp]), zero_mul]
  · have hc1 : c p.2 = 1 := hθ₀1 _ (by linarith only [hp2])
    have hW : IsOpen (vec3Ball 0 r₂) := isOpen_vec3Ball 0 r₂
    have hone : ∀ y ∈ vec3Ball 0 r₂, χ₀ y = 1 := fun y hy =>
      hχ₀one y (le_of_lt (by simpa [vec3Ball] using hy))
    have hp1' : p.1 - x₀ ∈ vec3Ball 0 r₂ := by
      rw [← mem_vec3Ball_iff_sub]
      exact hball_mono hrr₂.le hp1
    refine ⟨?_, fun γ hγ => ?_⟩
    · show c p.2 * χ₀ (p.1 - x₀) = 1
      rw [hc1, hone _ hp1', one_mul]
    · rw [spaceTimeWord_separated γ c hχ₀ x₀]
      simp only [wordDeriv_eq_zero_of_eqOn_one hW hone γ hγ _ hp1', mul_zero]

end ESS
