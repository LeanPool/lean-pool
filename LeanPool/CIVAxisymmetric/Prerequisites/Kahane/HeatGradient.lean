/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatPointwiseBound
public import LeanPool.CIVAxisymmetric.Reduction.MixedPartialSymmSpaceTimeSet
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.SliceCalculus
public import LeanPool.CIVAxisymmetric.Reduction.SpatialPartialCongrSpaceTimeSet
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus

/-!
# Interior gradient bounds for the heat operator and the Laplacian

From the pointwise heat-potential bound of the Serrin estimates, applied to `∂_l v` written as a
divergence, one spatial derivative is gained on a backward window with the scaling
`C (ρ sup |∂_t v - Δv| + sup |v| / ρ)`. Freezing time gives the same bound for the Laplacian on a
ball. These are the only analytic estimates in the derivative induction of
`thm:analytic:interior`; the pressure is handled at every order by the second one.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Interior gradient bound for the heat operator: on a backward window
`B_bar(x, ρ) × [s - ρ², s]` with `ρ ≤ 1`, `|∂_l v(x, s)| ≤ C (ρ sup |∂_t v - Δv| + sup |v| / ρ)`. -/
theorem heat_gradient_bound_spaceTimeSet :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ParabolicPoint → ℝ) (Ω : Set Vec3)
    (I : Set ℝ) (x : Vec3) (s ρ Λ M : ℝ), IsOpen Ω → IsOpen I → 0 < ρ → ρ ≤ 1 →
    {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ spaceTimeSet Ω I →
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => v z) (spaceTimeSet Ω I) →
    (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s,
      |timePartial v z - ∑ j, spatialSecondPartial v j j z| ≤ Λ) →
    (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s, |v z| ≤ M) →
    ∀ l : Fin 3, |spatialPartial v l (x, s)| ≤ C * (ρ * Λ + M / ρ) := by
  obtain ⟨C, hC, hHB⟩ := serrin_heat_pointwise_bound
  refine ⟨C, hC, ?_⟩
  intro v Ω I x s ρ Λ M hΩ hI hρ hρ1 hwin hv hΛ hM l
  have hO : IsOpen (X := Vec3 × ℝ) (spaceTimeSet Ω I) := hΩ.prod hI
  have hdiff : ∀ g : ParabolicPoint → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I) →
      ∀ z ∈ spaceTimeSet Ω I, DifferentiableAt ℝ (fun y : Vec3 => g (y, z.2)) z.1 := by
    intro g hg z hz
    have h1 : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) z :=
      (hg.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hz)
    exact h1.comp z.1 (differentiableAt_id.prodMk (differentiableAt_const _))
  have hv1 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial v j z)
      (spaceTimeSet Ω I) := fun j => contDiffOn_spatialPartial_spaceTimeSet hΩ hI hv j
  have hv2 : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialSecondPartial v j j z)
      (spaceTimeSet Ω I) := fun j =>
    contDiffOn_spatialPartial_spaceTimeSet (g := fun w => spatialPartial v j w) hΩ hI (hv1 j) j
  have hvt : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial v z) (spaceTimeSet Ω I) :=
    contDiffOn_timePartial_spaceTimeSet hΩ hI hv
  set Lv : ParabolicPoint → ℝ := fun z => timePartial v z - ∑ j, spatialSecondPartial v j j z
    with hLv_def
  have hLv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Lv z) (spaceTimeSet Ω I) :=
    hvt.sub (ContDiffOn.sum fun j _ => hv2 j)
  set U : Fin 3 → ParabolicPoint → ℝ := fun m => if m = l then v else fun _ => 0 with hU_def
  set Y : Fin 3 → ParabolicPoint → ℝ := fun m => if m = l then Lv else fun _ => 0 with hY_def
  have hzero : ∀ (m : Fin 3) (z : ParabolicPoint),
      spatialPartial (fun _ : ParabolicPoint => (0 : ℝ)) m z = 0 := by
    intro m z
    simp [spatialPartial]
  have hmem : ((x, s) : ParabolicPoint) ∈
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s := by
    refine ⟨?_, ?_, le_rfl⟩
    · change vec3EuclideanNorm (x - x) ≤ ρ
      rw [sub_self, vec3EuclideanNorm_zero]
      exact hρ.le
    · have : 0 ≤ ρ ^ 2 := sq_nonneg ρ
      change s - ρ ^ 2 ≤ s
      linarith only [this]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ _ hmem)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ hmem)
  refine hHB (fun z => spatialPartial v l z) U Y (spaceTimeSet Ω I) x s ρ Λ M hO hρ hρ1 hwin
    (hv1 l) (fun m => ?_) (fun m => ?_) (fun z hz => ?_) (fun z hz => ?_) (fun z hz m => ?_)
    (fun z hz m => ?_)
  · rw [hU_def]; dsimp only
    split_ifs
    · exact hv
    · exact contDiffOn_const
  · rw [hY_def]; dsimp only
    split_ifs
    · exact hLv
    · exact contDiffOn_const
  · rw [Finset.sum_eq_single l]
    · rw [hU_def]; dsimp only
      split_ifs with h
      · rfl
      · exact absurd rfl h
    · intro m _ hm
      rw [hU_def]; dsimp only
      split_ifs with h
      · exact absurd h hm
      · exact hzero m z
    · simp
  · rw [Finset.sum_eq_single (f := fun j => spatialPartial (Y j) j z) l]
    · rw [hY_def]; dsimp only
      split_ifs with h
      swap
      · exact absurd rfl h
      have hsumd : DifferentiableAt ℝ
          (fun y : Vec3 => ∑ j, spatialSecondPartial v j j (y, z.2)) z.1 :=
        hdiff (fun w => ∑ j, spatialSecondPartial v j j w)
          (ContDiffOn.sum (s := Finset.univ) fun j _ => hv2 j) z hz
      have hsub := spatialPartial_sub_of_differentiableAt (g := timePartial v)
        (h := fun w => ∑ j, spatialSecondPartial v j j w) (i := l) (hdiff _ hvt z hz) hsumd
      rw [hLv_def, hsub]
      have hsum : spatialPartial (fun w => ∑ j, spatialSecondPartial v j j w) l z =
          ∑ j, spatialPartial (fun w => spatialSecondPartial v j j w) l z := by
        simp only [Fin.sum_univ_three]
        rw [spatialPartial_add_of_differentiableAt
            ((hdiff _ (hv2 0) z hz).add (hdiff _ (hv2 1) z hz)) (hdiff _ (hv2 2) z hz),
          spatialPartial_add_of_differentiableAt (hdiff _ (hv2 0) z hz) (hdiff _ (hv2 1) z hz)]
      rw [hsum]
      have ht : timePartial (fun w => spatialPartial v l w) z =
          spatialPartial (timePartial v) l z :=
        (spatialPartial_timePartial_comm_spaceTimeSet hΩ hI hv hz l).symm
      have hs : ∀ j, spatialSecondPartial (fun w => spatialPartial v l w) j j z =
          spatialPartial (fun w => spatialSecondPartial v j j w) l z := by
        intro j
        have h1 : spatialPartial (fun w => spatialPartial (fun w' => spatialPartial v l w') j w) j z
            = spatialPartial (fun w => spatialPartial (fun w' => spatialPartial v j w') l w) j z :=
          spatialPartial_congr_of_eqOn_spaceTimeSet hΩ hI
            (fun w hw => spatialPartial_comm_spaceTimeSet hΩ w.2
              (contDiffOn_slice_of_spaceTimeSet hv hw.2) hw.1 l j) hz j
        have h2 := spatialPartial_comm_spaceTimeSet (g := fun w => spatialPartial v j w) hΩ z.2
          (contDiffOn_slice_of_spaceTimeSet (hv1 j) hz.2) hz.1 l j
        exact h1.trans h2
      rw [ht, Finset.sum_congr rfl fun j _ => hs j]
    · intro m _ hm
      rw [hY_def]; dsimp only
      split_ifs with h
      · exact absurd h hm
      · exact hzero m z
    · simp
  · rw [hY_def]; dsimp only
    split_ifs
    · exact hΛ z hz
    · rw [abs_zero]; exact hΛ0
  · rw [hU_def]; dsimp only
    split_ifs
    · exact hM z hz
    · rw [abs_zero]; exact hM0

/-- Interior gradient bound for the Laplacian on a closed ball `B_bar(x, ρ)`, `ρ ≤ 1`:
`|∂_l P(x)| ≤ C (ρ sup |ΔP| + sup |P| / ρ)`. -/
theorem laplace_gradient_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P : Vec3 → ℝ) (Ω : Set Vec3)
    (x : Vec3) (ρ Λ M : ℝ), IsOpen Ω → 0 < ρ → ρ ≤ 1 →
    {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ⊆ Ω → ContDiffOn ℝ (⊤ : ℕ∞) P Ω →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |∑ j, axisDeriv j (axisDeriv j P) y| ≤ Λ) →
    (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → |P y| ≤ M) →
    ∀ l : Fin 3, |axisDeriv l P x| ≤ C * (ρ * Λ + M / ρ) := by
  obtain ⟨C, hC, hHBG⟩ := heat_gradient_bound_spaceTimeSet
  refine ⟨C, hC, ?_⟩
  intro P Ω x ρ Λ M hΩ hρ hρ1 hball hP hΛ hM l
  have hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc ((0 : ℝ) - ρ ^ 2) 0 ⊆
      spaceTimeSet Ω (univ : Set ℝ) := fun z hz => ⟨hball hz.1, mem_univ _⟩
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => P z.1) (spaceTimeSet Ω (univ : Set ℝ)) :=
    hP.comp contDiffOn_fst fun z hz => hz.1
  have htime : ∀ z : ParabolicPoint, timePartial (fun w : ParabolicPoint => P w.1) z = 0 := by
    intro z
    simp [timePartial]
  have hsec : ∀ (z : ParabolicPoint) (j : Fin 3),
      spatialSecondPartial (fun w : ParabolicPoint => P w.1) j j z =
        axisDeriv j (axisDeriv j P) z.1 := fun z j => rfl
  have h := hHBG (fun w : ParabolicPoint => P w.1) Ω univ x 0 ρ Λ M hΩ isOpen_univ hρ hρ1 hwin hv
    (fun z hz => by
      rw [htime z, Finset.sum_congr rfl fun j _ => hsec z j, zero_sub, abs_neg]
      exact hΛ z.1 hz.1)
    (fun z hz => hM z.1 hz.1) l
  exact h

end CIV
