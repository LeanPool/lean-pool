/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.DzVelRotationInvariance
public import LeanPool.CIVAxisymmetric.Closure.MixedTermIntegrationByParts
public import LeanPool.CIVAxisymmetric.Closure.EllipticBoundsAnnulusBound

/-!
# The representative-to-Cartesian `L²` transfer for `eq:aniso:closure:mixed:bound`

The Cauchy–Schwarz step of the mixed-term estimate needs `L²` bounds, in terms of the tested
enstrophy `Y = cutoffEnstrophy χ u` and its dissipation `M = cutoffEnstrophyDissipation χ u`,
for the four cylindrical factors of `eq:aniso:closure:mixed` — `∂_r u_z`, `∂_z∂_r u_z`,
`ω_z`, `∂_z ω_z` — **read at the meridional representative** `meridional (polarR x) (x 2)` of
a general point `x`, since that is how `mixedTermFactorDz` is built. The elliptic and
div–curl bounds (`CIV.Closure.EllipticBoundsAnnulusBound`) instead bound these quantities read
at `x` itself.

The transfer is rotation invariance: `∂_r u_z` and `∂_z∂_r u_z` are each one term of a
Frobenius-norm sum (`gradientSq_eq_polarR`, `dzGradientSq_eq_polarR`) that agrees at `x` and at
its representative, and likewise `ω_z` and `∂_z ω_z` are each one term of a curl-energy sum
(`curlSq_eq_polarR`, and `gradientSq_eq_polarR` applied to the vorticity field itself, which is
axisymmetric by `isAxisymmetricOn_vorticityField`). Each pointwise domination integrates
directly against `χ²` and composes with the `x`-level bound.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### The polar representative map, on the open unit ball -/

theorem mixedTerm_continuousOn_repMap :
    ContinuousOn (fun x : Vec3 => meridional (polarR x) (x 2)) (vec3Ball (0 : Vec3) 1) := by
  have hc : Continuous (fun x : Vec3 => meridional (polarR x) (x 2)) := by
    unfold meridional
    have hc1 : Continuous (fun x : Vec3 => polarR x) := continuous_polarR
    have hc2 : Continuous (fun x : Vec3 => x 2) := continuous_apply 2
    fun_prop
  exact hc.continuousOn

theorem mixedTerm_mapsTo_repMap :
    Set.MapsTo (fun x : Vec3 => meridional (polarR x) (x 2))
      (vec3Ball (0 : Vec3) 1) (vec3Ball (0 : Vec3) 1) := fun _ hx => rep_mem_vec3Ball hx

/-! ### Global continuity and `L²` membership from a cutoff -/

/-- A function continuous on the unit ball and vanishing off the support of a compactly
supported cutoff inside it is continuous everywhere. -/
theorem continuous_of_continuousOn_cutoff {χ : Vec3 → ℝ}
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {F : Vec3 → ℝ}
    (hF : ContinuousOn F (vec3Ball (0 : Vec3) 1))
    (hzero : ∀ x : Vec3, x ∉ tsupport χ → F x = 0) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hF.continuousAt ((isOpen_vec3Ball 0 1).mem_nhds (hχU hx))
  · have heq : F =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      exact hzero y hy
    exact heq.continuousAt

/-- A function continuous on the unit ball and vanishing off the support of a compactly
supported cutoff inside it is in `L²`. -/
theorem memLp_two_of_cutoff {χ : Vec3 → ℝ} (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {F : Vec3 → ℝ}
    (hF : ContinuousOn F (vec3Ball (0 : Vec3) 1))
    (hzero : ∀ x : Vec3, x ∉ tsupport χ → F x = 0) :
    MemLp F 2 volume :=
  (continuous_of_continuousOn_cutoff hχU hF hzero).memLp_of_hasCompactSupport
    (HasCompactSupport.intro hχs hzero)

/-- The square of a function continuous on the unit ball and vanishing off the support of a
compactly supported cutoff inside it is integrable. -/
theorem integrable_sq_of_cutoff {χ : Vec3 → ℝ} (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {F : Vec3 → ℝ}
    (hF : ContinuousOn F (vec3Ball (0 : Vec3) 1))
    (hzero : ∀ x : Vec3, x ∉ tsupport χ → F x = 0) :
    Integrable (fun x : Vec3 => F x ^ 2) :=
  integrable_of_cutoff hχs hχU (hF.pow 2) (fun x hx => by rw [hzero x hx]; ring)

/-! ### `ω_z`, read at the representative, transfers to `Y` exactly -/

/-- The `χ`-weighted `L²` norm of `ω_z`, read at the meridional representative, is bounded by
the tested enstrophy `Y`: `ω_z` is one term of the rotation-invariant curl-energy sum. -/
theorem integral_sq_cutoff_mul_curlComp_two_rep_le {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    (∫ x : Vec3, (χ x * curlComp u 2 (meridional (polarR x) (x 2), t)) ^ 2)
      ≤ cutoffEnstrophy χ u t := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hpt : ∀ x : Vec3, (χ x * curlComp u 2 (meridional (polarR x) (x 2), t)) ^ 2
      ≤ χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    intro x
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) 1
    · have hz : (x, t) ∈ unitCylinder := ⟨hxb, ht⟩
      have hinv := curlSq_eq_polarR haxi hu1 hz
      have hle : (curlComp u 2 (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ i : Fin 3, (curlComp u i (meridional (polarR x) (x 2), t)) ^ 2 := by
        simp only [Fin.sum_univ_three]
        nlinarith only [sq_nonneg (curlComp u 0 (meridional (polarR x) (x 2), t)),
          sq_nonneg (curlComp u 1 (meridional (polarR x) (x 2), t))]
      rw [mul_pow, hinv]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hχU hm))
      have hR : (0 : ℝ) ≤ χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      rw [hχ0]
      nlinarith only [hR]
  have hLInt : Integrable (fun x : Vec3 =>
      (χ x * curlComp u 2 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs hχU
      (hχ.continuous.continuousOn.mul
        ((continuousOn_curl_slice hu 2 ht).comp' mixedTerm_continuousOn_repMap
          mixedTerm_mapsTo_repMap))
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hRInt : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) := by
    refine integrable_of_cutoff hχs hχU
      (((hχ.pow 2).continuous.continuousOn).mul
        (continuousOn_finsetSum Finset.univ fun i _ => (continuousOn_curl_slice hu i ht).pow 2))
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  have hcurlVecEq : (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3,
        (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2)
      = fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
    funext x
    have hpt' : ∀ i : Fin 3, curlVec (fun y : Vec3 => u (y, t)) x i = curlComp u i (x, t) :=
      fun i => by fin_cases i <;> rfl
    simp only [hpt']
  rw [cutoffEnstrophy_eq_integral_sq_curlVec χ u t, hcurlVecEq]
  exact integral_mono hLInt hRInt hpt

/-! ### `∂_z ω_z`, read at the representative, transfers to `M` exactly -/

/-- The `χ`-weighted `L²` norm of `∂_z ω_z`, read at the meridional representative, is bounded
by the enstrophy dissipation `M`: the vorticity field is itself axisymmetric
(`isAxisymmetricOn_vorticityField`), so `∂_z ω_z` is one term of the rotation-invariant
Frobenius-gradient sum of `ω`, which `M` already is
(`cutoffEnstrophyDissipation_eq_integral_sq_fderiv_curlVec`). -/
theorem integral_sq_cutoff_mul_dzcurlComp_two_rep_le {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball (0 : Vec3) 1) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    (∫ x : Vec3, (χ x
        * spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t)) ^ 2)
      ≤ cutoffEnstrophyDissipation χ u t := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hω1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => vorticityField u z) unitCylinder :=
    (contDiffOn_vorticityField hu).of_le (by exact_mod_cast le_top)
  have haxiω : IsAxisymmetricOn (vorticityField u) unitCylinder :=
    isAxisymmetricOn_vorticityField haxi hu1
  have hpt : ∀ x : Vec3, (χ x
        * spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t)) ^ 2
      ≤ χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2 := by
    intro x
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) 1
    · have hz : (x, t) ∈ unitCylinder := ⟨hxb, ht⟩
      have hinv := gradientSq_eq_polarR haxiω hω1 hz
      have hnn : ∀ i : Fin 3, (0 : ℝ) ≤ ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j
            (meridional (polarR x) (x 2), t)) ^ 2 :=
        fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hnn' : ∀ j : Fin 3, (0 : ℝ) ≤
          (spatialPartial (fun w => vorticityField u w 2) j
            (meridional (polarR x) (x 2), t)) ^ 2 := fun j => sq_nonneg _
      have hinner : (spatialPartial (fun w => vorticityField u w 2) 2
            (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ j : Fin 3, (spatialPartial (fun w => vorticityField u w 2) j
              (meridional (polarR x) (x 2), t)) ^ 2 :=
        Finset.single_le_sum (fun j _ => hnn' j) (Finset.mem_univ 2)
      have houter : (∑ j : Fin 3, (spatialPartial (fun w => vorticityField u w 2) j
            (meridional (polarR x) (x 2), t)) ^ 2)
          ≤ ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => vorticityField u w i) j
              (meridional (polarR x) (x 2), t)) ^ 2 :=
        Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ 2)
      have hle : (spatialPartial (fun w => vorticityField u w 2) 2
            (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => vorticityField u w i) j
              (meridional (polarR x) (x 2), t)) ^ 2 := le_trans hinner houter
      rw [mul_pow, hinv]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hχU hm))
      have hR : (0 : ℝ) ≤ χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => sq_nonneg _)
      rw [hχ0]
      nlinarith only [hR]
  have hLInt : Integrable (fun x : Vec3 => (χ x
      * spatialPartial (fun w => curlComp u 2 w) 2 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs hχU
      (hχ.continuous.continuousOn.mul
        ((continuousOn_dcurl_slice hu 2 2 ht).comp' mixedTerm_continuousOn_repMap
          mixedTerm_mapsTo_repMap))
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hRInt : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (spatialPartial (fun w => vorticityField u w i) j (x, t)) ^ 2) := by
    refine integrable_of_cutoff hχs hχU
      (((hχ.pow 2).continuous.continuousOn).mul
        (continuousOn_finsetSum Finset.univ fun i _ =>
          continuousOn_finsetSum Finset.univ fun j _ => (continuousOn_dcurl_slice hu i j ht).pow 2))
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  rw [cutoffEnstrophyDissipation_eq_integral_sq_fderiv_curlVec χ u t]
  exact integral_mono hLInt hRInt hpt

/-! ### `∂_r u_z`, read at the representative, transfers to `Y` up to a constant -/

/-- The `χ`-weighted `L²` norm of `∂_r u_z`, read at the meridional representative, is bounded
by `C (Y + 1)` for a constant `C` from the order-`≤ 1` annulus data: `∂_r u_z` is one term of
the rotation-invariant Frobenius-gradient sum of `u` (`gradientSq_eq_polarR`), and the full sum
is bounded at `x` itself by `integral_cutoff_sq_spatialPartial_le_of_multiPartial_le`. -/
theorem exists_integral_sq_cutoff_mul_firstPartial_rep_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, (χ x
          * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2)
        ≤ C * (cutoffEnstrophy χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  obtain ⟨C, hCnn, hC⟩ := integral_cutoff_sq_spatialPartial_le_of_multiPartial_le
    hsol hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound
  refine ⟨C, hCnn, fun t ht => ?_⟩
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hpt : ∀ x : Vec3, (χ x
        * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2
      ≤ χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => u w i) j (x, t)) ^ 2 := by
    intro x
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) 1
    · have hz : (x, t) ∈ unitCylinder := ⟨hxb, htmem⟩
      have hinv := gradientSq_eq_polarR haxi hu1 hz
      have hnn : ∀ i : Fin 3, (0 : ℝ) ≤ ∑ j : Fin 3,
          (spatialPartial (fun w => u w i) j (meridional (polarR x) (x 2), t)) ^ 2 :=
        fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hnn' : ∀ j : Fin 3, (0 : ℝ) ≤
          (spatialPartial (fun w => u w 2) j (meridional (polarR x) (x 2), t)) ^ 2 :=
        fun j => sq_nonneg _
      have hinner : (spatialPartial (fun w => u w 2) 0
            (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ j : Fin 3,
              (spatialPartial (fun w => u w 2) j (meridional (polarR x) (x 2), t)) ^ 2 :=
        Finset.single_le_sum (fun j _ => hnn' j) (Finset.mem_univ 0)
      have houter : (∑ j : Fin 3,
            (spatialPartial (fun w => u w 2) j (meridional (polarR x) (x 2), t)) ^ 2)
          ≤ ∑ i : Fin 3, ∑ j : Fin 3,
              (spatialPartial (fun w => u w i) j (meridional (polarR x) (x 2), t)) ^ 2 :=
        Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ 2)
      have hle : (spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ i : Fin 3, ∑ j : Fin 3,
              (spatialPartial (fun w => u w i) j (meridional (polarR x) (x 2), t)) ^ 2 :=
        le_trans hinner houter
      rw [mul_pow, hinv]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hρ1 (hρU hm)))
      have hR : (0 : ℝ) ≤ χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (spatialPartial (fun w => u w i) j (x, t)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => sq_nonneg _)
      rw [hχ0]
      nlinarith only [hR]
  have hLInt : Integrable (fun x : Vec3 => (χ x
      * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs (hρU.trans hρ1)
      (hχ.continuous.continuousOn.mul
        ((continuousOn_dvel_slice hu 2 0 htmem).comp' mixedTerm_continuousOn_repMap
          mixedTerm_mapsTo_repMap))
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hRInt : Integrable (fun x : Vec3 =>
      χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, (spatialPartial (fun w => u w i) j (x, t)) ^ 2) := by
    refine integrable_of_cutoff hχs (hρU.trans hρ1)
      (((hχ.pow 2).continuous.continuousOn).mul
        (continuousOn_finsetSum Finset.univ fun i _ =>
          continuousOn_finsetSum Finset.univ fun j _ => (continuousOn_dvel_slice hu i j
            htmem).pow 2))
      (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]; ring
  exact le_trans (integral_mono hLInt hRInt hpt) (hC t ht)

/-! ### `∂_z∂_r u_z`, read at the representative, transfers to `M` up to a constant -/

/-- The `χ`-weighted `L²` norm of `∂_z∂_r u_z`, read at the meridional representative, is
bounded by `C (M + 1)` for a constant `C` from the order-`≤ 2` annulus data: `∂_z∂_r u_z`
commutes to `∂_r∂_z u_z` (`spatialSecondPartial_comm`), which is one term of the
rotation-invariant Frobenius-gradient sum of `∂_z u` (`dzGradientSq_eq_polarR`), and the full
sum is bounded at `x` itself by `integral_cutoff_sq_spatialSecondPartial_le_of_multiPartial_le`. -/
theorem exists_integral_sq_cutoff_mul_secondPartial_rep_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, (χ x
          * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2)
        ≤ C * (cutoffEnstrophyDissipation χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  obtain ⟨C, hCnn, hC⟩ := integral_cutoff_sq_spatialSecondPartial_le_of_multiPartial_le
    hsol hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound
  refine ⟨C, hCnn, fun t ht => ?_⟩
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hpt : ∀ x : Vec3, (χ x
        * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2
      ≤ χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2 := by
    intro x
    by_cases hxb : x ∈ vec3Ball (0 : Vec3) 1
    · have hz : (x, t) ∈ unitCylinder := ⟨hxb, htmem⟩
      have hzrep : ((meridional (polarR x) (x 2) : Vec3), t) ∈ unitCylinder :=
        ⟨rep_mem_vec3Ball hxb, htmem⟩
      have hcomm : spatialSecondPartial (fun w => u w 2) 0 2
            (meridional (polarR x) (x 2), t)
          = spatialSecondPartial (fun w => u w 2) 2 0 (meridional (polarR x) (x 2), t) :=
        spatialSecondPartial_comm (contDiffOn_component hu 2) hzrep 0 2
      -- Step 1: at the representative, the single term is at most the two-index sum.
      have hnnRep : ∀ i : Fin 3, (0 : ℝ) ≤ ∑ j : Fin 3,
          (spatialSecondPartial (fun w => u w i) 2 j
            (meridional (polarR x) (x 2), t)) ^ 2 :=
        fun i => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hnnRep' : ∀ j : Fin 3, (0 : ℝ) ≤
          (spatialSecondPartial (fun w => u w 2) 2 j
            (meridional (polarR x) (x 2), t)) ^ 2 := fun j => sq_nonneg _
      have hinnerRep : (spatialSecondPartial (fun w => u w 2) 2 0
            (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ j : Fin 3, (spatialSecondPartial (fun w => u w 2) 2 j
              (meridional (polarR x) (x 2), t)) ^ 2 :=
        Finset.single_le_sum (fun j _ => hnnRep' j) (Finset.mem_univ 0)
      have houterRep : (∑ j : Fin 3, (spatialSecondPartial (fun w => u w 2) 2 j
            (meridional (polarR x) (x 2), t)) ^ 2)
          ≤ ∑ i : Fin 3, ∑ j : Fin 3, (spatialSecondPartial (fun w => u w i) 2 j
              (meridional (polarR x) (x 2), t)) ^ 2 :=
        Finset.single_le_sum (fun i _ => hnnRep i) (Finset.mem_univ 2)
      have hleRep : (spatialSecondPartial (fun w => u w 2) 2 0
            (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ i : Fin 3, ∑ j : Fin 3, (spatialSecondPartial (fun w => u w i) 2 j
              (meridional (polarR x) (x 2), t)) ^ 2 := le_trans hinnerRep houterRep
      -- Step 2: the two-index sum transfers from the representative to `x`.
      have hinv := dzGradientSq_eq_polarR haxi hu hz
      -- Step 3: at `x`, the two-index sum (outer index fixed at `2`) is at most the full
      -- three-index sum.
      have hnnX : ∀ i : Fin 3, (0 : ℝ) ≤ ∑ j : Fin 3, ∑ k : Fin 3,
          (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2 :=
        fun i => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
      have houterX : (∑ i : Fin 3, ∑ j : Fin 3,
            (spatialSecondPartial (fun w => u w i) 2 j (x, t)) ^ 2)
          ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
              (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum
          (f := fun j : Fin 3 => ∑ k : Fin 3, (spatialSecondPartial (fun w => u w i) j k (x, t))
            ^ 2)
          (fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ 2)
      have hle : (spatialSecondPartial (fun w => u w 2) 2 0
            (meridional (polarR x) (x 2), t)) ^ 2
          ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
              (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2 := by
        rw [← hinv] at hleRep
        exact le_trans hleRep houterX
      rw [hcomm, mul_pow]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hxb (hρ1 (hρU hm)))
      have hR : (0 : ℝ) ≤ χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2 :=
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
      rw [hχ0]
      nlinarith only [hR]
  have hLInt : Integrable (fun x : Vec3 => (χ x
      * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2) := by
    refine integrable_sq_of_cutoff hχs (hρU.trans hρ1) ?_
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
    have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => spatialSecondPartial (fun w => u w 2) 0 2 (y, t))
        (vec3Ball (0 : Vec3) 1) :=
      ((contDiffOn_slice_partial hu 2 0 htmem).fderiv_of_isOpen (isOpen_vec3Ball 0 1)
        (by simp)).clm_apply contDiffOn_const
    exact hχ.continuous.continuousOn.mul
      ((hsmooth.continuousOn.comp' mixedTerm_continuousOn_repMap mixedTerm_mapsTo_repMap))
  have hRInt : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (spatialSecondPartial (fun w => u w i) j k (x, t)) ^ 2) := by
    refine integrable_of_cutoff hχs (hρU.trans hρ1)
      (((hχ.pow 2).continuous.continuousOn).mul
        (continuousOn_finsetSum Finset.univ fun i _ =>
          continuousOn_finsetSum Finset.univ fun j _ =>
            continuousOn_finsetSum Finset.univ fun k _ => ?_))
      (fun x hx => ?_)
    · have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y : Vec3 => spatialSecondPartial (fun w => u w i) j k (y, t))
          (vec3Ball (0 : Vec3) 1) :=
        ((contDiffOn_slice_partial hu i j htmem).fderiv_of_isOpen (isOpen_vec3Ball 0 1)
          (by simp)).clm_apply contDiffOn_const
      exact hsm.continuousOn.pow 2
    · rw [image_eq_zero_of_notMem_tsupport hx]; ring
  exact le_trans (integral_mono hLInt hRInt hpt) (hC t ht)

/-! ### The two representative-level bounds, multiplied by the swirl factor -/

/-- The `χ`-weighted `L²` norm of `u_θ · ∂_z∂_r u_z`, both read at the meridional
representative, is bounded by `W² C (M + 1)`: `|u_θ| ≤ W` on `tsupport χ` (`hW`), and the
`∂_z∂_r u_z` factor alone is bounded by `C (M + 1)`
(`exists_integral_sq_cutoff_mul_secondPartial_rep_le`). -/
theorem exists_integral_sq_swirl_mul_cutoff_mul_secondPartial_rep_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu)
    {W : ℝ → ℝ}
    (hW : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, (u (meridional (polarR x) (x 2), t) 1 * χ x
          * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2)
        ≤ W t ^ 2 * C * (cutoffEnstrophyDissipation χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  obtain ⟨C, hCnn, hC⟩ := exists_integral_sq_cutoff_mul_secondPartial_rep_le
    hsol haxi hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound
  refine ⟨C, hCnn, fun t ht => ?_⟩
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hsmoothA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Vec3 => spatialSecondPartial (fun w => u w 2) 0 2 (y, t))
      (vec3Ball (0 : Vec3) 1) :=
    ((contDiffOn_slice_partial hu 2 0 htmem).fderiv_of_isOpen (isOpen_vec3Ball 0 1)
      (by simp)).clm_apply contDiffOn_const
  have hcontA : ContinuousOn
      (fun x : Vec3 => spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) :=
    hsmoothA.continuousOn.comp' mixedTerm_continuousOn_repMap mixedTerm_mapsTo_repMap
  have hcontSwirl : ContinuousOn (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1)
      (vec3Ball (0 : Vec3) 1) :=
    (continuousOn_vel_slice hu 1 htmem).comp' mixedTerm_continuousOn_repMap
      mixedTerm_mapsTo_repMap
  have hgInt : Integrable (fun x : Vec3 =>
      (χ x * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs (hρU.trans hρ1) (hχ.continuous.continuousOn.mul hcontA)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hfInt : Integrable (fun x : Vec3 => (u (meridional (polarR x) (x 2), t) 1 * χ x
      * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs (hρU.trans hρ1)
      ((hcontSwirl.mul hχ.continuous.continuousOn).mul hcontA)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hpt : ∀ x : Vec3, (u (meridional (polarR x) (x 2), t) 1 * χ x
        * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2
      ≤ W t ^ 2 * (χ x
          * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2 := by
    intro x
    by_cases hxχ : x ∈ tsupport χ
    · have hxρ : meridional (polarR x) (x 2) ∈ vec3Ball (0 : Vec3) ρ :=
        rep_mem_vec3Ball (hρU hxχ)
      have hbd : |u (meridional (polarR x) (x 2), t) 1| ≤ W t :=
        hW t ht (polarR x) (x 2) hxρ
      have hsq : (u (meridional (polarR x) (x 2), t) 1) ^ 2 ≤ (W t) ^ 2 := by
        nlinarith only [hbd, abs_nonneg (u (meridional (polarR x) (x 2), t) 1),
          sq_abs (u (meridional (polarR x) (x 2), t) 1)]
      have hRnn : (0:ℝ) ≤ (χ x
          * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2 :=
        sq_nonneg _
      nlinarith only [hsq, hRnn]
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
      have hWnnsq : (0:ℝ) ≤ W t ^ 2 := sq_nonneg _
      rw [hχ0]
      nlinarith only [hWnnsq]
  have hstep : (∫ x : Vec3, (u (meridional (polarR x) (x 2), t) 1 * χ x
        * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2)
      ≤ ∫ x : Vec3, W t ^ 2 * (χ x
          * spatialSecondPartial (fun w => u w 2) 0 2 (meridional (polarR x) (x 2), t)) ^ 2 :=
    integral_mono hfInt (hgInt.const_mul _) hpt
  rw [integral_const_mul] at hstep
  have hfinal := hC t ht
  nlinarith only [hstep, mul_le_mul_of_nonneg_left hfinal (sq_nonneg (W t))]

/-- The `χ`-weighted `L²` norm of `u_θ · ∂_r u_z`, both read at the meridional representative,
is bounded by `W² C (Y + 1)`: `|u_θ| ≤ W` on `tsupport χ` (`hW`), and the `∂_r u_z` factor
alone is bounded by `C (Y + 1)` (`exists_integral_sq_cutoff_mul_firstPartial_rep_le`). -/
theorem exists_integral_sq_swirl_mul_cutoff_mul_firstPartial_rep_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    {ρ : ℝ} (hρU : tsupport χ ⊆ vec3Ball (0 : Vec3) ρ)
    (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Rm Rp Mu : ℝ}
    (hAsub : A ⊆ {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp})
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu)
    {W : ℝ → ℝ}
    (hW : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        |u (meridional x₁ x₃, t) 1| ≤ W t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      (∫ x : Vec3, (u (meridional (polarR x) (x 2), t) 1 * χ x
          * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2)
        ≤ W t ^ 2 * C * (cutoffEnstrophy χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  obtain ⟨C, hCnn, hC⟩ := exists_integral_sq_cutoff_mul_firstPartial_rep_le
    hsol haxi hχ hχs hρU hρ1 ht₀ hAcl hχA hAsub hbound
  refine ⟨C, hCnn, fun t ht => ?_⟩
  have htmem : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hcontA : ContinuousOn
      (fun x : Vec3 => spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t))
      (vec3Ball (0 : Vec3) 1) :=
    (continuousOn_dvel_slice hu 2 0 htmem).comp' mixedTerm_continuousOn_repMap
      mixedTerm_mapsTo_repMap
  have hcontSwirl : ContinuousOn (fun x : Vec3 => u (meridional (polarR x) (x 2), t) 1)
      (vec3Ball (0 : Vec3) 1) :=
    (continuousOn_vel_slice hu 1 htmem).comp' mixedTerm_continuousOn_repMap
      mixedTerm_mapsTo_repMap
  have hgInt : Integrable (fun x : Vec3 =>
      (χ x * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs (hρU.trans hρ1) (hχ.continuous.continuousOn.mul hcontA)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hfInt : Integrable (fun x : Vec3 => (u (meridional (polarR x) (x 2), t) 1 * χ x
      * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2) :=
    integrable_sq_of_cutoff hχs (hρU.trans hρ1)
      ((hcontSwirl.mul hχ.continuous.continuousOn).mul hcontA)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx]; ring)
  have hpt : ∀ x : Vec3, (u (meridional (polarR x) (x 2), t) 1 * χ x
        * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2
      ≤ W t ^ 2 * (χ x
          * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2 := by
    intro x
    by_cases hxχ : x ∈ tsupport χ
    · have hxρ : meridional (polarR x) (x 2) ∈ vec3Ball (0 : Vec3) ρ :=
        rep_mem_vec3Ball (hρU hxχ)
      have hbd : |u (meridional (polarR x) (x 2), t) 1| ≤ W t :=
        hW t ht (polarR x) (x 2) hxρ
      have hsq : (u (meridional (polarR x) (x 2), t) 1) ^ 2 ≤ (W t) ^ 2 := by
        nlinarith only [hbd, abs_nonneg (u (meridional (polarR x) (x 2), t) 1),
          sq_abs (u (meridional (polarR x) (x 2), t) 1)]
      have hRnn : (0:ℝ) ≤ (χ x
          * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2 :=
        sq_nonneg _
      nlinarith only [hsq, hRnn]
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
      have hWnnsq : (0:ℝ) ≤ W t ^ 2 := sq_nonneg _
      rw [hχ0]
      nlinarith only [hWnnsq]
  have hstep : (∫ x : Vec3, (u (meridional (polarR x) (x 2), t) 1 * χ x
        * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2)
      ≤ ∫ x : Vec3, W t ^ 2 * (χ x
          * spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)) ^ 2 :=
    integral_mono hfInt (hgInt.const_mul _) hpt
  rw [integral_const_mul] at hstep
  have hfinal := hC t ht
  nlinarith only [hstep, mul_le_mul_of_nonneg_left hfinal (sq_nonneg (W t))]

end CIV
