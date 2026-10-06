/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityDivCurlSmooth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Whole-space div–curl estimates for smooth fields

The higher order estimate in `lem:local-div-curl` is obtained by applying the
compactly supported smooth div–curl identity to each ordered derivative.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem localDivCurlSmooth_wordDeriv_compact {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (α : List (Fin 3)) :
    HasCompactSupport (wordDeriv α f) := by
  induction α generalizing f with
  | nil => simpa [wordDeriv] using hf
  | cons j α ih =>
      simpa [wordDeriv] using
        ih (f := spatialDeriv f j) (hasCompactSupport_spatialDeriv hf j)

private theorem localDivCurlSmooth_wordDeriv_add
    (α : List (Fin 3)) {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    wordDeriv α (fun x => f x + g x) =
      fun x => wordDeriv α f x + wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hsum : spatialDeriv (fun x => f x + g x) j =
          fun x => spatialDeriv f j x + spatialDeriv g j x := by
        funext x
        exact spatialDeriv_add ((hf.differentiable (by simp)) x)
          ((hg.differentiable (by simp)) x) j
      rw [wordDeriv, hsum]
      have hfa : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_spatialDeriv_smooth hf j
      have hga : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_spatialDeriv_smooth hg j
      simp only [wordDeriv]
      exact ih hfa hga

private theorem localDivCurlSmooth_wordDeriv_sub
    (α : List (Fin 3)) {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    wordDeriv α (fun x => f x - g x) =
      fun x => wordDeriv α f x - wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hsub : spatialDeriv (fun x => f x - g x) j =
          fun x => spatialDeriv f j x - spatialDeriv g j x := by
        funext x
        have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
          (fderiv_fun_sub ((hf.differentiable (by simp)) x)
            ((hg.differentiable (by simp)) x))
        simpa [spatialDeriv] using h
      rw [wordDeriv, hsub]
      have hfa : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
        contDiff_spatialDeriv_smooth hf j
      have hga : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
        contDiff_spatialDeriv_smooth hg j
      simp only [wordDeriv]
      exact ih hfa hga

theorem localDivCurlSmooth_wordDeriv_spatialDeriv
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 3)) (j : Fin 3) :
    wordDeriv α (spatialDeriv f j) =
      spatialDeriv (wordDeriv α f) j := by
  induction α generalizing f with
  | nil => rfl
  | cons k α ih =>
      rw [wordDeriv, wordDeriv]
      have hswap : spatialDeriv (spatialDeriv f j) k =
          spatialDeriv (spatialDeriv f k) j := by
        funext x
        exact vorticityDivCurlSmooth_deriv_comm hf k j x
      rw [hswap]
      have hfk : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f k) :=
        contDiff_spatialDeriv_smooth hf k
      rw [ih hfk]

theorem localDivCurlSmooth_wordDeriv_sum
    (α : List (Fin 3)) {f : Fin 3 → Vec3 → ℝ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) :
    wordDeriv α (fun x => ∑ i : Fin 3, f i x) =
      fun x => ∑ i : Fin 3, wordDeriv α (f i) x := by
  induction α generalizing f with
  | nil => rfl
  | cons j α ih =>
      have hsum : spatialDeriv (fun x => ∑ i : Fin 3, f i x) j =
          fun x => ∑ i : Fin 3, spatialDeriv (f i) j x := by
        funext x
        simp only [spatialDeriv]
        have hfd : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
            DifferentiableAt ℝ (f i) x := by
          intro i hi
          exact ((hf i).differentiable (by simp)) x
        rw [fderiv_fun_sum hfd]
        simp
      rw [wordDeriv, hsum]
      have hderiv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (f i) j) :=
        fun i => contDiff_spatialDeriv_smooth (hf i) j
      simp only [wordDeriv]
      exact ih hderiv

private theorem localDivCurlSmooth_wordDeriv_append
    {f : Vec3 → ℝ} (α : List (Fin 3)) (j : Fin 3) :
    wordDeriv (α ++ [j]) f = spatialDeriv (wordDeriv α f) j := by
  induction α generalizing f with
  | nil => rfl
  | cons k α ih =>
      change wordDeriv (α ++ [j]) (spatialDeriv f k) =
        spatialDeriv (wordDeriv (k :: α) f) j
      rw [ih (f := spatialDeriv f k)]
      rfl

private theorem localDivCurlSmooth_antisymmetric_eq_curl
    (V : Fin 3 → Vec3 → ℝ) (x : Vec3) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      (spatialDeriv (V b) a x - spatialDeriv (V a) b x) ^ 2) =
      2 * ∑ k : Fin 3,
        (spatialDeriv (V (k + 2)) (k + 1) x -
          spatialDeriv (V (k + 1)) (k + 2) x) ^ 2 := by
  simp only [Fin.sum_univ_three]
  norm_num [Fin.add_def]
  ring

private theorem localDivCurlSmooth_derivative_energy
    {V : Fin 3 → Vec3 → ℝ}
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) (α : List (Fin 3)) :
    ∫ x, ∑ a : Fin 3, ∑ b : Fin 3,
        spatialDeriv (wordDeriv α (V b)) a x ^ 2 ≤
      ∫ x, (wordDeriv α (fun y => ∑ i : Fin 3, spatialDeriv (V i) i y) x) ^ 2 +
        2 * ∑ k : Fin 3,
          wordDeriv α (fun y =>
            spatialDeriv (V (k + 2)) (k + 1) y -
              spatialDeriv (V (k + 1)) (k + 2) y) x ^ 2 := by
  let W : Fin 3 → Vec3 → ℝ := fun i => wordDeriv α (V i)
  have hW : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (W i) := fun i =>
    contDiff_wordDeriv (hV i) α
  have hWc : ∀ i, HasCompactSupport (W i) := fun i =>
    localDivCurlSmooth_wordDeriv_compact (hVc i) α
  have hbase := vorticityDivCurlSmooth_integral_le hW hWc
  have hdiv : ∀ x,
      ∑ i : Fin 3, spatialDeriv (W i) i x =
        wordDeriv α (fun y => ∑ i : Fin 3, spatialDeriv (V i) i y) x := by
    intro x
    have hsum := localDivCurlSmooth_wordDeriv_sum α
      (f := fun i => spatialDeriv (V i) i)
      (fun i => contDiff_spatialDeriv_smooth (hV i) i)
    calc
      ∑ i : Fin 3, spatialDeriv (W i) i x =
          ∑ i : Fin 3, wordDeriv α (spatialDeriv (V i) i) x := by
            simp only [W]
            refine Finset.sum_congr rfl fun i _ => ?_
            exact (congrFun
              (localDivCurlSmooth_wordDeriv_spatialDeriv (hV i) α i) x).symm
      _ = wordDeriv α (fun y => ∑ i : Fin 3, spatialDeriv (V i) i y) x :=
        (congrFun hsum x).symm
  have hcurl : ∀ k x,
      spatialDeriv (W (k + 2)) (k + 1) x - spatialDeriv (W (k + 1)) (k + 2) x =
        wordDeriv α (fun y =>
          spatialDeriv (V (k + 2)) (k + 1) y -
            spatialDeriv (V (k + 1)) (k + 2) y) x := by
    intro k x
    have hsub := localDivCurlSmooth_wordDeriv_sub α
      (f := spatialDeriv (V (k + 2)) (k + 1))
      (g := spatialDeriv (V (k + 1)) (k + 2))
      (contDiff_spatialDeriv_smooth (hV (k + 2)) (k + 1))
      (contDiff_spatialDeriv_smooth (hV (k + 1)) (k + 2))
    calc
      _ = wordDeriv α (spatialDeriv (V (k + 2)) (k + 1)) x -
          wordDeriv α (spatialDeriv (V (k + 1)) (k + 2)) x := by
          simp only [W]
          rw [(congrFun
            (localDivCurlSmooth_wordDeriv_spatialDeriv (hV (k + 2)) α (k + 1)) x).symm,
            (congrFun
            (localDivCurlSmooth_wordDeriv_spatialDeriv (hV (k + 1)) α (k + 2)) x).symm]
      _ = _ := (congrFun hsub x).symm
  have hpoint : ∀ x,
      (∑ i : Fin 3, spatialDeriv (W i) i x) ^ 2 +
        ∑ a : Fin 3, ∑ b : Fin 3,
          (spatialDeriv (W b) a x - spatialDeriv (W a) b x) ^ 2 =
        (wordDeriv α (fun y => ∑ i : Fin 3, spatialDeriv (V i) i y) x) ^ 2 +
          2 * ∑ k : Fin 3,
            wordDeriv α (fun y =>
              spatialDeriv (V (k + 2)) (k + 1) y -
                spatialDeriv (V (k + 1)) (k + 2) y) x ^ 2 := by
    intro x
    rw [hdiv x, localDivCurlSmooth_antisymmetric_eq_curl W x]
    simp_rw [hcurl]
  calc
    _ ≤ ∫ x, ((∑ i : Fin 3, spatialDeriv (W i) i x) ^ 2 +
          ∑ a : Fin 3, ∑ b : Fin 3,
            (spatialDeriv (W b) a x - spatialDeriv (W a) b x) ^ 2) := hbase
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x

/-- Spatial derivative words of the highest order in the div–curl estimate. -/
@[expose] def localDivCurlSmoothTopWords (m : ℕ) : Finset (List (Fin 3)) :=
  (sobolevWords (m + 1)).filter (fun α => α.length = m + 1)

/-- Highest-order derivative words paired with a spatial coordinate. -/
@[expose] def localDivCurlSmoothTopPairs (m : ℕ) :
    Finset ((List (Fin 3)) × Fin 3) :=
  ((sobolevWords m).filter (fun α => α.length = m)).product Finset.univ

private theorem localDivCurlSmooth_topWords_eq_image (m : ℕ) :
    localDivCurlSmoothTopWords m =
      (localDivCurlSmoothTopPairs m).image (fun p => p.1 ++ [p.2]) := by
  classical
  ext β
  constructor
  · intro hβ
    have hlen : β.length = m + 1 := (Finset.mem_filter.mp hβ).2
    have hne : β ≠ [] := by
      intro h
      simp [h] at hlen
    refine Finset.mem_image.mpr ⟨(β.dropLast, β.getLast hne), ?_, ?_⟩
    · rw [localDivCurlSmoothTopPairs]
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · apply mem_sobolevWords.mpr
          rw [List.length_dropLast, hlen]
          omega
        · rw [List.length_dropLast, hlen]
          omega
      · exact Finset.mem_univ _
    · exact List.dropLast_append_getLast hne
  · intro hβ
    rcases Finset.mem_image.mp hβ with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hα, _⟩
    rcases Finset.mem_filter.mp hα with ⟨hαw, hαlen⟩
    simp only [localDivCurlSmoothTopWords, Finset.mem_filter,
      mem_sobolevWords]
    rw [List.length_append, List.length_singleton, hαlen]
    constructor
    · omega
    · rfl

private theorem localDivCurlSmooth_words_succ_eq_union (m : ℕ) :
    sobolevWords (m + 1) = sobolevWords m ∪ localDivCurlSmoothTopWords m := by
  ext α
  simp only [Finset.mem_union, mem_sobolevWords, localDivCurlSmoothTopWords,
    Finset.mem_filter, mem_sobolevWords]
  omega

private theorem localDivCurlSmooth_words_top_disjoint (m : ℕ) :
    Disjoint (sobolevWords m) (localDivCurlSmoothTopWords m) := by
  rw [Finset.disjoint_left]
  intro α hα htop
  have hα' : α.length ≤ m := (mem_sobolevWords).mp hα
  have htop' : α.length = m + 1 := (Finset.mem_filter.mp htop).2
  omega

private theorem localDivCurlSmooth_sq_hasCompactSupport {f : Vec3 → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (fun x => f x ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact hfc.isCompact
  intro x hx
  apply subset_tsupport
  apply Function.mem_support.mpr
  intro hzero
  apply Function.mem_support.mp hx
  simp [hzero]

private theorem localDivCurlSmooth_sq_integrable {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2) (volume : Measure Vec3) :=
  (hf.continuous.pow 2).integrable_of_hasCompactSupport
    (localDivCurlSmooth_sq_hasCompactSupport hfc)

private theorem localDivCurlSmooth_sum_topWords_bij (m : ℕ)
    {F : List (Fin 3) → ℝ} {G : (List (Fin 3) × Fin 3) → ℝ}
    (hcomp : ∀ p ∈ localDivCurlSmoothTopPairs m,
      F (p.1 ++ [p.2]) = G p) :
    ∑ β ∈ localDivCurlSmoothTopWords m, F β =
      ∑ p ∈ localDivCurlSmoothTopPairs m, G p := by
  classical
  let i : ∀ β, β ∈ localDivCurlSmoothTopWords m → (List (Fin 3) × Fin 3) :=
    fun β hβ => ⟨β.dropLast, β.getLast (by
      intro hnil
      have hlen := (Finset.mem_filter.mp hβ).2
      simp [hnil] at hlen)⟩
  let j : ∀ p, p ∈ localDivCurlSmoothTopPairs m → List (Fin 3) :=
    fun p _ => p.1 ++ [p.2]
  have hi : ∀ β hβ, i β hβ ∈ localDivCurlSmoothTopPairs m := by
    intro β hβ
    have hlen : β.length = m + 1 := (Finset.mem_filter.mp hβ).2
    have hdrop : β.dropLast.length = m := by
      rw [List.length_dropLast, hlen]
      omega
    rw [localDivCurlSmoothTopPairs]
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply mem_sobolevWords.mpr
        change β.dropLast.length ≤ m
        exact hdrop.le
      · exact hdrop
    · exact Finset.mem_univ _
  have hj : ∀ p hp, j p hp ∈ localDivCurlSmoothTopWords m := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hα, _⟩
    rcases Finset.mem_filter.mp hα with ⟨hαw, hαlen⟩
    simp only [localDivCurlSmoothTopWords, Finset.mem_filter]
    constructor
    · exact (mem_sobolevWords).2 (by simp [j, hαlen])
    · simp [j, hαlen]
  have hleft : ∀ β hβ, j (i β hβ) (hi β hβ) = β := by
    intro β hβ
    have hne : β ≠ [] := by
      intro hnil
      have hlen := (Finset.mem_filter.mp hβ).2
      simp [hnil] at hlen
    exact List.dropLast_append_getLast hne
  have hright : ∀ p hp, i (j p hp) (hj p hp) = p := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hα, _⟩
    rcases Finset.mem_filter.mp hα with ⟨_, hαlen⟩
    apply Prod.ext
    · simp [i, j]
    · simp [i, j]
  apply Finset.sum_bij' i j hi hj hleft hright
  intro β hβ
  calc
    F β = F (j (i β hβ) (hi β hβ)) := congrArg F (hleft β hβ).symm
    _ = G (i β hβ) := hcomp (i β hβ) (hi β hβ)

private theorem localDivCurlSmooth_derivative_sq_integrable
    {V : Fin 3 → Vec3 → ℝ} (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) (i j : Fin 3)
    (α : List (Fin 3)) :
    Integrable (fun x => spatialDeriv (wordDeriv α (V i)) j x ^ 2)
      (volume : Measure Vec3) := by
  apply localDivCurlSmooth_sq_integrable
  · exact contDiff_spatialDeriv_smooth
      (contDiff_wordDeriv (hV i) α) j
  · exact hasCompactSupport_spatialDeriv
      (localDivCurlSmooth_wordDeriv_compact (hVc i) α) j

private theorem localDivCurlSmooth_derivative_sum_integral
    {V : Fin 3 → Vec3 → ℝ} (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) (α : List (Fin 3)) :
    (∑ j : Fin 3, ∑ i : Fin 3,
      ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2) =
      ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
  calc
    _ = ∑ j : Fin 3, ∫ x,
        ∑ i : Fin 3, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← integral_finsetSum _ (fun i _ =>
            localDivCurlSmooth_derivative_sq_integrable hV hVc i j α)]
    _ = ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
          rw [← integral_finsetSum _ (fun j _ =>
            integrable_finsetSum _ (fun i _ =>
              localDivCurlSmooth_derivative_sq_integrable hV hVc i j α))]

private theorem localDivCurlSmooth_wordDeriv_sq_integrable
    {V : Fin 3 → Vec3 → ℝ} (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) (i : Fin 3)
    (α : List (Fin 3)) :
    Integrable (fun x => wordDeriv α (V i) x ^ 2) (volume : Measure Vec3) :=
  localDivCurlSmooth_sq_integrable
    (contDiff_wordDeriv (hV i) α)
    (localDivCurlSmooth_wordDeriv_compact (hVc i) α)

private theorem localDivCurlSmooth_normSq_succ_eq
    {V : Fin 3 → Vec3 → ℝ} (m : ℕ) (i : Fin 3) :
    sobolevNormSqOn (m + 1) univ (fun α => wordDeriv α (V i)) =
      sobolevNormSqOn m univ (fun α => wordDeriv α (V i)) +
        ∑ α ∈ localDivCurlSmoothTopWords m,
          ∫ x, wordDeriv α (V i) x ^ 2 := by
  rw [sobolevNormSqOn, sobolevNormSqOn,
    localDivCurlSmooth_words_succ_eq_union,
    Finset.sum_union (localDivCurlSmooth_words_top_disjoint m)]
  simp only [Measure.restrict_univ]

private theorem localDivCurlSmooth_topPair_sum_le_gradient_sum
    {V : Fin 3 → Vec3 → ℝ} (m : ℕ)
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) :
    (∑ i : Fin 3, ∑ p ∈ localDivCurlSmoothTopPairs m,
      ∫ x, spatialDeriv (wordDeriv p.1 (V i)) p.2 x ^ 2) ≤
      ∑ α ∈ sobolevWords m,
        ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
          spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
  let T := (sobolevWords m).filter (fun α => α.length = m)
  have hstep₁ :
      (∑ i : Fin 3, ∑ p ∈ localDivCurlSmoothTopPairs m,
        ∫ x, spatialDeriv (wordDeriv p.1 (V i)) p.2 x ^ 2) =
      ∑ i : Fin 3, ∑ α ∈ T, ∑ j : Fin 3,
        ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ p ∈ T.product Finset.univ,
      ∫ x, spatialDeriv (wordDeriv p.1 (V i)) p.2 x ^ 2) = _
    exact Finset.sum_product T Finset.univ
      (fun p => ∫ x, spatialDeriv (wordDeriv p.1 (V i)) p.2 x ^ 2)
  have hstep₂ :
      (∑ i : Fin 3, ∑ α ∈ T, ∑ j : Fin 3,
        ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2) =
      ∑ α ∈ T, ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
    calc
      _ = ∑ α ∈ T, ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
            rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := T)
              (f := fun i α => ∑ j : Fin 3,
                ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2)]
      _ = ∑ α ∈ T, ∑ j : Fin 3, ∑ i : Fin 3,
          ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
            apply Finset.sum_congr rfl
            intro α hα
            rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
              (t := (Finset.univ : Finset (Fin 3)))
              (f := fun i j => ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2)]
  have hstep₃ :
      (∑ α ∈ T, ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2) =
      ∑ α ∈ T, ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
    apply Finset.sum_congr rfl
    intro α hα
    exact localDivCurlSmooth_derivative_sum_integral hV hVc α
  have hTsub : T ⊆ sobolevWords m := by
    simp [T]
  have hnonneg (α : List (Fin 3)) :
      0 ≤ ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => sq_nonneg _
  calc
    _ = ∑ i : Fin 3, ∑ α ∈ T, ∑ j : Fin 3,
        ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := hstep₁
    _ = ∑ α ∈ T, ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x, spatialDeriv (wordDeriv α (V i)) j x ^ 2 := hstep₂
    _ = ∑ α ∈ T, ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2 := hstep₃
    _ ≤ ∑ α ∈ sobolevWords m, ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun α hα hαT => hnonneg α)

private theorem localDivCurlSmooth_norm_succ_le
    {V : Fin 3 → Vec3 → ℝ} (m : ℕ)
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) :
    (∑ i : Fin 3, sobolevNormSqOn (m + 1) univ
      (fun α => wordDeriv α (V i))) ≤
      (∑ i : Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (V i))) +
        ∑ α ∈ sobolevWords m,
          ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
            spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
  have htop : ∀ i : Fin 3,
      (∑ α ∈ localDivCurlSmoothTopWords m,
        ∫ x, wordDeriv α (V i) x ^ 2) =
      ∑ p ∈ localDivCurlSmoothTopPairs m,
        ∫ x, spatialDeriv (wordDeriv p.1 (V i)) p.2 x ^ 2 := by
    intro i
    have hbij := localDivCurlSmooth_sum_topWords_bij m
      (F := fun α => ∫ x, wordDeriv α (V i) x ^ 2)
      (G := fun p => ∫ x, wordDeriv (p.1 ++ [p.2]) (V i) x ^ 2)
      (fun p hp => rfl)
    simpa only [localDivCurlSmooth_wordDeriv_append] using hbij
  calc
    _ = ∑ i : Fin 3,
        (sobolevNormSqOn m univ (fun α => wordDeriv α (V i)) +
          ∑ α ∈ localDivCurlSmoothTopWords m,
            ∫ x, wordDeriv α (V i) x ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact localDivCurlSmooth_normSq_succ_eq m i
    _ = (∑ i : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (V i))) +
        ∑ i : Fin 3, ∑ p ∈ localDivCurlSmoothTopPairs m,
          ∫ x, spatialDeriv (wordDeriv p.1 (V i)) p.2 x ^ 2 := by
          rw [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact htop i
    _ ≤ _ := add_le_add_right
      (localDivCurlSmooth_topPair_sum_le_gradient_sum m hV hVc)
      (∑ i : Fin 3, sobolevNormSqOn m univ (fun α => wordDeriv α (V i)))

/-- The divergence of a vector field given by its components. -/
@[expose] def localDivCurlSmoothDiv (V : Fin 3 → Vec3 → ℝ) : Vec3 → ℝ :=
  fun x => ∑ i : Fin 3, spatialDeriv (V i) i x

/-- A component of the curl of a vector field. -/
@[expose] def localDivCurlSmoothCurl (V : Fin 3 → Vec3 → ℝ) (k : Fin 3) : Vec3 → ℝ :=
  fun x => spatialDeriv (V (k + 2)) (k + 1) x -
    spatialDeriv (V (k + 1)) (k + 2) x

private theorem localDivCurlSmooth_div_contDiff
    {V : Fin 3 → Vec3 → ℝ} (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i)) :
    ContDiff ℝ (⊤ : ℕ∞) (localDivCurlSmoothDiv V) := by
  have h0 := contDiff_spatialDeriv_smooth (hV 0) 0
  have h1 := contDiff_spatialDeriv_smooth (hV 1) 1
  have h2 := contDiff_spatialDeriv_smooth (hV 2) 2
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i : Fin 3, spatialDeriv (V i) i x)
  simp only [Fin.sum_univ_three]
  exact (h0.add h1).add h2

private theorem localDivCurlSmooth_div_compact
    {V : Fin 3 → Vec3 → ℝ} (hVc : ∀ i, HasCompactSupport (V i)) :
    HasCompactSupport (localDivCurlSmoothDiv V) := by
  have h0 := hasCompactSupport_spatialDeriv (hVc 0) 0
  have h1 := hasCompactSupport_spatialDeriv (hVc 1) 1
  have h2 := hasCompactSupport_spatialDeriv (hVc 2) 2
  change HasCompactSupport (fun x => ∑ i : Fin 3, spatialDeriv (V i) i x)
  simp only [Fin.sum_univ_three]
  exact (h0.add h1).add h2

private theorem localDivCurlSmooth_curl_contDiff
    {V : Fin 3 → Vec3 → ℝ} (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (localDivCurlSmoothCurl V k) :=
  (contDiff_spatialDeriv_smooth (hV (k + 2)) (k + 1)).sub
    (contDiff_spatialDeriv_smooth (hV (k + 1)) (k + 2))

private theorem localDivCurlSmooth_curl_compact
    {V : Fin 3 → Vec3 → ℝ} (hVc : ∀ i, HasCompactSupport (V i))
    (k : Fin 3) : HasCompactSupport (localDivCurlSmoothCurl V k) :=
  (hasCompactSupport_spatialDeriv (hVc (k + 2)) (k + 1)).add
    (hasCompactSupport_spatialDeriv (hVc (k + 1)) (k + 2)).neg

private theorem localDivCurlSmooth_divCurl_gradient_le
    {V : Fin 3 → Vec3 → ℝ} (m : ℕ)
    (hV : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) :
    (∑ α ∈ sobolevWords m,
      ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
        spatialDeriv (wordDeriv α (V i)) j x ^ 2) ≤
      sobolevNormSqOn m univ
          (fun α => wordDeriv α (localDivCurlSmoothDiv V)) +
        2 * ∑ k : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (localDivCurlSmoothCurl V k)) := by
  have hper : ∀ α ∈ sobolevWords m,
      ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
          spatialDeriv (wordDeriv α (V i)) j x ^ 2 ≤
        ∫ x, (wordDeriv α (fun y =>
            ∑ i : Fin 3, spatialDeriv (V i) i y) x) ^ 2 +
          2 * ∑ k : Fin 3, wordDeriv α (fun y =>
            spatialDeriv (V (k + 2)) (k + 1) y -
              spatialDeriv (V (k + 1)) (k + 2) y) x ^ 2 := by
    intro α _
    exact localDivCurlSmooth_derivative_energy hV hVc α
  have hdivInt (α : List (Fin 3)) :
      Integrable (fun x => wordDeriv α (localDivCurlSmoothDiv V) x ^ 2)
        (volume : Measure Vec3) :=
    localDivCurlSmooth_sq_integrable
      (contDiff_wordDeriv
        (localDivCurlSmooth_div_contDiff hV) α)
      (localDivCurlSmooth_wordDeriv_compact
        (localDivCurlSmooth_div_compact hVc) α)
  have hcurlInt (α : List (Fin 3)) (k : Fin 3) :
      Integrable (fun x => wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2)
        (volume : Measure Vec3) :=
    localDivCurlSmooth_sq_integrable
      (contDiff_wordDeriv
        (localDivCurlSmooth_curl_contDiff hV k) α)
      (localDivCurlSmooth_wordDeriv_compact
        (localDivCurlSmooth_curl_compact hVc k) α)
  have hsplit (α : List (Fin 3)) :
      ∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2 +
          2 * ∑ k : Fin 3,
            wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 =
        (∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2) +
          2 * ∑ k : Fin 3,
            ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 := by
    have hsum : Integrable (fun x => ∑ k : Fin 3,
        wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2) (volume : Measure Vec3) :=
      integrable_finsetSum _ fun k _ => hcurlInt α k
    rw [integral_add (hdivInt α) (hsum.const_mul 2), integral_const_mul,
      integral_finsetSum _ (fun k _ => hcurlInt α k)]
  have hsumdata :
      (∑ α ∈ sobolevWords m,
        ((∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2) +
          2 * ∑ k : Fin 3,
            ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2)) =
      sobolevNormSqOn m univ
          (fun α => wordDeriv α (localDivCurlSmoothDiv V)) +
        2 * ∑ k : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (localDivCurlSmoothCurl V k)) := by
    calc
      _ = (∑ α ∈ sobolevWords m,
            (∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2)) +
          ∑ α ∈ sobolevWords m,
            2 * ∑ k : Fin 3,
              ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 :=
        Finset.sum_add_distrib
      _ = (∑ α ∈ sobolevWords m,
            (∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2)) +
          2 * ∑ α ∈ sobolevWords m, ∑ k : Fin 3,
              ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 := by
        rw [Finset.mul_sum]
      _ = (∑ α ∈ sobolevWords m,
            (∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2)) +
          2 * ∑ k : Fin 3, ∑ α ∈ sobolevWords m,
              ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 := by
        rw [Finset.sum_comm (s := sobolevWords m)
          (t := (Finset.univ : Finset (Fin 3)))
          (f := fun α k => ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2)]
      _ = _ := by
        simp [sobolevNormSqOn, Measure.restrict_univ]
  have hper' : ∀ α ∈ sobolevWords m,
      ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
          spatialDeriv (wordDeriv α (V i)) j x ^ 2 ≤
        (∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2) +
          2 * ∑ k : Fin 3,
            ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 := by
    intro α hα
    calc
      _ ≤ ∫ x, (wordDeriv α (fun y =>
            ∑ i : Fin 3, spatialDeriv (V i) i y) x) ^ 2 +
          2 * ∑ k : Fin 3,
            wordDeriv α (fun y =>
              spatialDeriv (V (k + 2)) (k + 1) y -
                spatialDeriv (V (k + 1)) (k + 2) y) x ^ 2 := hper α hα
      _ = (∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2) +
          2 * ∑ k : Fin 3,
            ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2 := by
        exact hsplit α
  calc
    _ ≤ ∑ α ∈ sobolevWords m,
        ((∫ x, wordDeriv α (localDivCurlSmoothDiv V) x ^ 2) +
          2 * ∑ k : Fin 3,
            ∫ x, wordDeriv α (localDivCurlSmoothCurl V k) x ^ 2) :=
      Finset.sum_le_sum (fun α hα => hper' α hα)
    _ = _ := hsumdata

/-- Whole-space higher order div–curl estimate for compactly supported smooth fields
(`lem:local-div-curl`). -/
theorem divCurl_smooth_whole (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (V i)) → (∀ i, HasCompactSupport (V i)) →
      ∑ i, sobolevNormSqOn (m + 1) univ (fun α => wordDeriv α (V i)) ≤
        C * (sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x =>
                ∑ i : Fin 3, spatialDeriv (V i) i x)) +
            ∑ k : Fin 3, sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x =>
                spatialDeriv (V (k + 2)) (k + 1) x -
                  spatialDeriv (V (k + 1)) (k + 2) x)) +
            ∑ i, sobolevNormSqOn m univ (fun α => wordDeriv α (V i))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro V hV hVc
  let H : ℝ := ∑ i : Fin 3,
    sobolevNormSqOn m univ (fun α => wordDeriv α (V i))
  let D : ℝ := sobolevNormSqOn m univ
    (fun α => wordDeriv α (localDivCurlSmoothDiv V))
  let Curls : ℝ := ∑ k : Fin 3,
    sobolevNormSqOn m univ
      (fun α => wordDeriv α (localDivCurlSmoothCurl V k))
  have hH0 : 0 ≤ H := by
    dsimp [H]
    apply Finset.sum_nonneg
    intro i hi
    simp only [sobolevNormSqOn, Measure.restrict_univ]
    apply Finset.sum_nonneg
    intro α hα
    exact integral_nonneg fun x => sq_nonneg _
  have hD0 : 0 ≤ D := by
    dsimp [D]
    simp only [sobolevNormSqOn, Measure.restrict_univ]
    apply Finset.sum_nonneg
    intro α hα
    exact integral_nonneg fun x => sq_nonneg _
  have hCurls0 : 0 ≤ Curls := by
    dsimp [Curls]
    apply Finset.sum_nonneg
    intro k hk
    simp only [sobolevNormSqOn, Measure.restrict_univ]
    apply Finset.sum_nonneg
    intro α hα
    exact integral_nonneg fun x => sq_nonneg _
  have hcoeff : H + (D + 2 * Curls) ≤ 2 * (D + Curls + H) := by
    nlinarith only [hH0, hD0, hCurls0]
  calc
    (∑ i : Fin 3, sobolevNormSqOn (m + 1) univ
        (fun α => wordDeriv α (V i))) ≤ H +
        ∑ α ∈ sobolevWords m, ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
          spatialDeriv (wordDeriv α (V i)) j x ^ 2 := by
            exact localDivCurlSmooth_norm_succ_le m hV hVc
    _ ≤ H + (D + 2 * Curls) := by
          exact add_le_add_right (localDivCurlSmooth_divCurl_gradient_le m hV hVc) H
    _ ≤ 2 * (D + Curls + H) := by
          exact hcoeff

end ESS
