/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.HeatGradient
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.MixedCalculus
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.LeibnizExpansion

/-!
# One spatial derivative more for the velocity and the pressure

The heat gradient bound applied to `∂^α uᵢ`, whose heat residual is `∂^α` of the forced
Navier–Stokes right-hand side, and the Laplace gradient bound applied to the time slice of
`∂^α p`, whose Laplacian is `∂^α (div f − ∑ᵢⱼ ∂ᵢuⱼ ∂ⱼuᵢ)`, bound every derivative of order `k + 1`
by `ρ` times the order-`k` source and `1/ρ` times the order-`k` field. The products are bounded
with the multi-index Leibniz rule. This is the one-step estimate of the induction in the proof of
`thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- A multi-index of order `k + 1` is a multi-index of order `k` plus one unit direction. -/
theorem exists_eq_add_single_of_order_succ {β : Fin 3 → ℕ} {k : ℕ}
    (hβ : β 0 + β 1 + β 2 = k + 1) :
    ∃ (l : Fin 3) (α : Fin 3 → ℕ), β = α + Pi.single l 1 ∧ α 0 + α 1 + α 2 = k := by
  have key : ∀ l : Fin 3, 1 ≤ β l → ∃ α : Fin 3 → ℕ, β = α + Pi.single l 1 ∧
      α 0 + α 1 + α 2 = k := by
    intro l hl
    refine ⟨β - Pi.single l 1, ?_, ?_⟩
    · ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      split_ifs with h
      · subst h; omega
      · omega
    · simp only [Pi.sub_apply, Pi.single_apply]
      fin_cases l <;> simp at hl ⊢ <;> omega
  by_cases h0 : 1 ≤ β 0
  · exact ⟨0, key 0 h0⟩
  by_cases h1 : 1 ≤ β 1
  · exact ⟨1, key 1 h1⟩
  exact ⟨2, key 2 (by omega)⟩

/-- Adding one unit direction raises the order by one. -/
theorem order_add_single (α : Fin 3 → ℕ) (l : Fin 3) :
    (α + Pi.single l 1 : Fin 3 → ℕ) 0 + (α + Pi.single l 1 : Fin 3 → ℕ) 1 +
      (α + Pi.single l 1 : Fin 3 → ℕ) 2 =
      α 0 + α 1 + α 2 + 1 := by
  fin_cases l <;> simp <;> omega

/-- One spatial derivative more for the velocity: with window bounds `c m` on the velocity
derivatives of order `m ≤ k + 1`, `P` on the pressure derivatives of order `k + 1` and `F` on the
force derivatives of order `k`, every velocity derivative of order `k + 1` at the top of the
window is at most `C (ρ (F + 3 ∑ₘ C(k,m) c m c (k+1-m) + P) + c k / ρ)`. -/
theorem kahane_velocity_step : ∃ C : ℝ, 0 < C ∧
    ∀ (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
      (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω → IsOpen I →
      IsClassicalSolutionOn u p f (spaceTimeSet Ω I) →
      ∀ (x : Vec3) (t ρ : ℝ) (k : ℕ) (c : ℕ → ℝ) (P F : ℝ), 0 < ρ → ρ ≤ 1 →
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t ⊆ spaceTimeSet Ω I →
      (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 ≤ k + 1 → ∀ j : Fin 3,
          |multiPartial (fun w => u w j) γ z| ≤ c (γ 0 + γ 1 + γ 2)) →
      (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 → |multiPartial p γ z| ≤ P) →
      (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k → ∀ i : Fin 3,
          |multiPartial (fun w => f w i) γ z| ≤ F) →
      ∀ β : Fin 3 → ℕ, β 0 + β 1 + β 2 = k + 1 → ∀ i : Fin 3,
        |multiPartial (fun w => u w i) β (x, t)| ≤
          C * (ρ * (F + 3 * ∑ m ∈ Finset.range (k + 1),
            (k.choose m : ℝ) * (c m * c (k + 1 - m)) + P) + c k / ρ) := by
  obtain ⟨C, hC, hHBG⟩ := heat_gradient_bound_spaceTimeSet
  refine ⟨C, hC, ?_⟩
  intro u p f Ω I hΩ hI hsol x t ρ k c P F hρ hρ1 hwin hc hP hF β hβ i
  obtain ⟨l, α, rfl, hα⟩ := exists_eq_add_single_of_order_succ hβ
  have hui : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w i)
      (spaceTimeSet Ω I) := fun i => contDiffOn_pi.1 hsol.1 i
  have hmem : ((x, t) : ParabolicPoint) ∈
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t := by
    refine ⟨?_, ?_, le_rfl⟩
    · show vec3EuclideanNorm (x - x) ≤ ρ
      rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le
    · have : 0 ≤ ρ ^ 2 := sq_nonneg ρ
      show t - ρ ^ 2 ≤ t
      linarith only [this]
  have hxt := hwin hmem
  have hshift : multiPartial (fun w => u w i) (α + Pi.single l 1) (x, t) =
      spatialPartial (multiPartial (fun w => u w i) α) l (x, t) :=
    (axisDeriv_multiPartial_slice_eq hΩ t (contDiffOn_slice_of_spaceTimeSet (hui i) hxt.2) α l
      hxt.1).symm
  -- the heat residual of `∂^α uᵢ`
  have hΛ : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      |timePartial (multiPartial (fun w => u w i) α) z -
        ∑ j, spatialSecondPartial (multiPartial (fun w => u w i) α) j j z| ≤
        F + 3 * ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c m * c (k + 1 - m)) + P := by
    intro z hz
    have hzS := hwin hz
    rw [momentum_multiPartial_spaceTimeSet hΩ hI hsol hzS α i]
    have hFz : |multiPartial (fun w => f w i) α z| ≤ F := hF z hz α hα i
    have hPz : |multiPartial p (α + Pi.single i 1) z| ≤ P :=
      hP z hz _ (by rw [order_add_single, hα])
    have hprod : ∀ j : Fin 3,
        |multiPartial (fun w => u w j * spatialPartial (fun w' => u w' i) j w) α z| ≤
          ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c m * c (k + 1 - m)) := by
      intro j
      have hml := abs_multiPartial_mul_le (g := fun w => u w j)
        (h := fun w => spatialPartial (fun w' => u w' i) j w) hΩ z.2
        (contDiffOn_slice_of_spaceTimeSet (hui j) hzS.2)
        (contDiffOn_slice_spatialPartial hΩ z.2
          (contDiffOn_slice_of_spaceTimeSet (hui i) hzS.2) j) hzS.1 α c (fun m => c (m + 1))
        (fun γ hγ => by
          have hle : γ 0 + γ 1 + γ 2 ≤ k + 1 := by
            have := hγ 0; have := hγ 1; have := hγ 2; omega
          exact hc z hz γ hle j)
        (fun γ hγ => by
          have hle : γ 0 + γ 1 + γ 2 ≤ k := by
            have := hγ 0; have := hγ 1; have := hγ 2; omega
          rw [multiPartial_spatialPartial_spaceTimeSet hΩ z.2
            (contDiffOn_slice_of_spaceTimeSet (hui i) hzS.2) hzS.1 γ j]
          have := hc z hz (γ + Pi.single j 1) (by rw [order_add_single]; omega) i
          rwa [order_add_single] at this)
      rw [hα] at hml
      refine hml.trans (le_of_eq (Finset.sum_congr rfl fun m hm => ?_))
      rw [Finset.mem_range] at hm
      rw [show k - m + 1 = k + 1 - m by omega]
    have hsum : |∑ j, multiPartial (fun w => u w j * spatialPartial (fun w' => u w' i) j w) α z| ≤
        3 * ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c m * c (k + 1 - m)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => hprod j).trans (le_of_eq ?_)
      simp
    calc _ ≤ |multiPartial (fun w => f w i) α z -
            ∑ j, multiPartial (fun w => u w j * spatialPartial (fun w' => u w' i) j w) α z| +
          |multiPartial p (α + Pi.single i 1) z| := abs_sub _ _
      _ ≤ |multiPartial (fun w => f w i) α z| +
            |∑ j, multiPartial (fun w => u w j * spatialPartial (fun w' => u w' i) j w) α z| +
          |multiPartial p (α + Pi.single i 1) z| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith only [hFz, hPz, hsum]
  have hM : ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
      |multiPartial (fun w => u w i) α z| ≤ c k := by
    intro z hz
    have := hc z hz α (by omega) i
    rwa [hα] at this
  rw [hshift]
  exact hHBG (multiPartial (fun w => u w i) α) Ω I x t ρ _ (c k) hΩ hI hρ hρ1 hwin
    (contDiffOn_multiPartial_spaceTimeSet hΩ hI (hui i) α) hΛ hM l

/-- One spatial derivative more for the pressure: with bounds `c m` on the velocity derivatives
of order `m ≤ k + 1` on the time slice of `B̄(x, ρ)`, `Q` on the pressure derivatives of order
`k` and `F` on the force derivatives of order `k + 1` there, every pressure derivative of order
`k + 1` at `x` is at most `C (ρ (3 F + 9 ∑ₘ C(k,m) c (m+1) c (k+1-m)) + Q / ρ)`. -/
theorem kahane_pressure_step : ∃ C : ℝ, 0 < C ∧
    ∀ (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
      (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω → IsOpen I →
      IsClassicalSolutionOn u p f (spaceTimeSet Ω I) →
      ∀ (x : Vec3) (t ρ : ℝ) (k : ℕ) (c : ℕ → ℝ) (Q F : ℝ), 0 < ρ → ρ ≤ 1 → t ∈ I →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → y ∈ Ω) →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 ≤ k + 1 → ∀ j : Fin 3,
          |multiPartial (fun w => u w j) γ (y, t)| ≤ c (γ 0 + γ 1 + γ 2)) →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k → |multiPartial p γ (y, t)| ≤ Q) →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 → ∀ i : Fin 3,
          |multiPartial (fun w => f w i) γ (y, t)| ≤ F) →
      ∀ β : Fin 3 → ℕ, β 0 + β 1 + β 2 = k + 1 →
        |multiPartial p β (x, t)| ≤
          C * (ρ * (3 * F + 9 * ∑ m ∈ Finset.range (k + 1),
            (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m))) + Q / ρ) := by
  obtain ⟨C, hC, hHBF⟩ := laplace_gradient_bound
  refine ⟨C, hC, ?_⟩
  intro u p f Ω I hΩ hI hsol x t ρ k c Q F hρ hρ1 ht hball hc hQ hF β hβ
  obtain ⟨l, α, rfl, hα⟩ := exists_eq_add_single_of_order_succ hβ
  have hui : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w i)
      (spaceTimeSet Ω I) := fun i => contDiffOn_pi.1 hsol.1 i
  have hfi : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w i)
      (spaceTimeSet Ω I) := fun i => contDiffOn_pi.1 hsol.2.2.1 i
  have hps : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => p (y, t)) Ω :=
    contDiffOn_slice_of_spaceTimeSet hsol.2.1 ht
  have hx : x ∈ Ω := hball x (by rw [sub_self, vec3EuclideanNorm_zero]; exact hρ.le)
  have sl : ∀ (g : ParabolicPoint → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) (spaceTimeSet Ω I) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => g (y, t)) Ω :=
    fun g hg => contDiffOn_slice_of_spaceTimeSet hg ht
  have hdu : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => spatialPartial (fun w => u w j) i (y, t))
      Ω := fun i j => contDiffOn_slice_spatialPartial hΩ t (sl _ (hui j)) i
  have hdf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => spatialPartial (fun w => f w i) i (y, t))
      Ω := fun i => contDiffOn_slice_spatialPartial hΩ t (sl _ (hfi i)) i
  -- bound on the Laplacian of `∂^α p`
  have hΛ : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
      |∑ j, axisDeriv j (axisDeriv j (fun y' : Vec3 => multiPartial p α (y', t))) y| ≤
        3 * F + 9 * ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m)) := by
    intro y hy
    have hyΩ := hball y hy
    have hyS : ((y, t) : ParabolicPoint) ∈ spaceTimeSet Ω I := ⟨hyΩ, ht⟩
    have e1 : ∑ j, axisDeriv j (axisDeriv j (fun y' : Vec3 => multiPartial p α (y', t))) y =
        multiPartial (fun w => ∑ j, spatialSecondPartial p j j w) α (y, t) :=
      sum_spatialSecondPartial_multiPartial_spaceTimeSet hΩ t hps hyΩ α
    have e2 : multiPartial (fun w => ∑ j, spatialSecondPartial p j j w) α (y, t) =
        multiPartial (fun w => ∑ i, spatialPartial (fun w' => f w' i) i w -
          ∑ i, ∑ j, spatialPartial (fun w' => u w' j) i w *
            spatialPartial (fun w' => u w' i) j w) α (y, t) :=
      multiPartial_congr_of_eqOn_spaceTimeSet hΩ hI
        (fun w hw => pressure_poisson_spaceTimeSet hΩ hI hsol hw) α hyS
    have hdivf : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y' : Vec3 => ∑ i, spatialPartial (fun w' => f w' i) i (y', t)) Ω :=
      ContDiffOn.sum fun i _ => hdf i
    have hprodS : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : Vec3 => ∑ j,
        spatialPartial (fun w' => u w' j) i (y', t) * spatialPartial (fun w' => u w' i) j (y', t))
        Ω := fun i => ContDiffOn.sum fun j _ => (hdu i j).mul (hdu j i)
    have hQQ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : Vec3 => ∑ i, ∑ j,
        spatialPartial (fun w' => u w' j) i (y', t) * spatialPartial (fun w' => u w' i) j (y', t))
        Ω := ContDiffOn.sum fun i _ => hprodS i
    rw [e1, e2, multiPartial_sub_slice hΩ t hdivf hQQ α hyΩ,
      multiPartial_fin3_sum hΩ t hdf α hyΩ, multiPartial_fin3_sum hΩ t hprodS α hyΩ]
    have hF1 : |∑ i, multiPartial (fun w => spatialPartial (fun w' => f w' i) i w) α (y, t)| ≤
        3 * F := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ i : Fin 3,
          |multiPartial (fun w => spatialPartial (fun w' => f w' i) i w) α (y, t)| ≤ F := by
        intro i
        have e := multiPartial_spatialPartial_spaceTimeSet hΩ t (sl _ (hfi i)) hyΩ α i
        have := hF y hy (α + Pi.single i 1) (by rw [order_add_single, hα]) i
        exact (le_of_eq (congrArg abs e)).trans this
      refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
      simp
    have hprod : ∀ i j : Fin 3, |multiPartial (fun w => spatialPartial (fun w' => u w' j) i w *
        spatialPartial (fun w' => u w' i) j w) α (y, t)| ≤
          ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m)) := by
      intro i j
      have hbd : ∀ (a b : Fin 3) (γ : Fin 3 → ℕ), (∀ n, γ n ≤ α n) →
          |multiPartial (fun w => spatialPartial (fun w' => u w' a) b w) γ (y, t)| ≤
            c (γ 0 + γ 1 + γ 2 + 1) := by
        intro a b γ hγ
        have hle : γ 0 + γ 1 + γ 2 ≤ k := by
          have := hγ 0; have := hγ 1; have := hγ 2; omega
        have e := multiPartial_spatialPartial_spaceTimeSet hΩ t (sl _ (hui a)) hyΩ γ b
        have := hc y hy (γ + Pi.single b 1) (by rw [order_add_single]; omega) a
        rw [order_add_single] at this
        exact (le_of_eq (congrArg abs e)).trans this
      have hml := abs_multiPartial_mul_le (g := fun w => spatialPartial (fun w' => u w' j) i w)
        (h := fun w => spatialPartial (fun w' => u w' i) j w) hΩ t (hdu i j) (hdu j i) hyΩ α
        (fun m => c (m + 1)) (fun m => c (m + 1)) (fun γ hγ => hbd j i γ hγ)
        (fun γ hγ => hbd i j γ hγ)
      rw [hα] at hml
      refine hml.trans (le_of_eq (Finset.sum_congr rfl fun m hm => ?_))
      rw [Finset.mem_range] at hm
      rw [show k - m + 1 = k + 1 - m by omega]
    have hQ2 : |∑ i, multiPartial (fun w => ∑ j, spatialPartial (fun w' => u w' j) i w *
        spatialPartial (fun w' => u w' i) j w) α (y, t)| ≤
        9 * ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ i : Fin 3, |multiPartial (fun w => ∑ j, spatialPartial (fun w' => u w' j) i w *
          spatialPartial (fun w' => u w' i) j w) α (y, t)| ≤
          3 * ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m)) := by
        intro i
        rw [multiPartial_fin3_sum hΩ t (fun j => (hdu i j).mul (hdu j i)) α hyΩ]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun j _ => hprod i j).trans (le_of_eq ?_)
        simp
      refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
      simp
      ring
    calc _ ≤ _ := abs_sub _ _
      _ ≤ _ := add_le_add hF1 hQ2
  have hM : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
      |(fun y' : Vec3 => multiPartial p α (y', t)) y| ≤ Q :=
    fun y hy => hQ y hy α hα
  have h := hHBF (fun y' : Vec3 => multiPartial p α (y', t)) Ω x ρ _ Q hΩ hρ hρ1
    (fun y hy => hball y hy) (contDiffOn_multiPartial_slice hΩ t hps α) hΛ hM l
  rw [axisDeriv_multiPartial_slice_eq hΩ t hps α l hx] at h
  exact h

/-- The velocity and pressure steps with one common constant `C ≥ 1`. -/
theorem kahane_velocity_pressure_step : ∃ C : ℝ, 1 ≤ C ∧
    (∀ (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
      (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω → IsOpen I →
      IsClassicalSolutionOn u p f (spaceTimeSet Ω I) →
      ∀ (x : Vec3) (t ρ : ℝ) (k : ℕ) (c : ℕ → ℝ) (P F : ℝ), 0 < ρ → ρ ≤ 1 →
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t ⊆ spaceTimeSet Ω I →
      (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 ≤ k + 1 → ∀ j : Fin 3,
          |multiPartial (fun w => u w j) γ z| ≤ c (γ 0 + γ 1 + γ 2)) →
      (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 → |multiPartial p γ z| ≤ P) →
      (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (t - ρ ^ 2) t,
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k → ∀ i : Fin 3,
          |multiPartial (fun w => f w i) γ z| ≤ F) →
      ∀ β : Fin 3 → ℕ, β 0 + β 1 + β 2 = k + 1 → ∀ i : Fin 3,
        |multiPartial (fun w => u w i) β (x, t)| ≤
          C * (ρ * (F + 3 * ∑ m ∈ Finset.range (k + 1),
            (k.choose m : ℝ) * (c m * c (k + 1 - m)) + P) + c k / ρ)) ∧
    (∀ (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
      (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω → IsOpen I →
      IsClassicalSolutionOn u p f (spaceTimeSet Ω I) →
      ∀ (x : Vec3) (t ρ : ℝ) (k : ℕ) (c : ℕ → ℝ) (Q F : ℝ), 0 < ρ → ρ ≤ 1 → t ∈ I →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ → y ∈ Ω) →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 ≤ k + 1 → ∀ j : Fin 3,
          |multiPartial (fun w => u w j) γ (y, t)| ≤ c (γ 0 + γ 1 + γ 2)) →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k → |multiPartial p γ (y, t)| ≤ Q) →
      (∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ ρ →
        ∀ γ : Fin 3 → ℕ, γ 0 + γ 1 + γ 2 = k + 1 → ∀ i : Fin 3,
          |multiPartial (fun w => f w i) γ (y, t)| ≤ F) →
      ∀ β : Fin 3 → ℕ, β 0 + β 1 + β 2 = k + 1 →
        |multiPartial p β (x, t)| ≤
          C * (ρ * (3 * F + 9 * ∑ m ∈ Finset.range (k + 1),
            (k.choose m : ℝ) * (c (m + 1) * c (k + 1 - m))) + Q / ρ)) := by
  obtain ⟨C₁, hC₁, hvel⟩ := kahane_velocity_step
  obtain ⟨C₂, hC₂, hpres⟩ := kahane_pressure_step
  have up : ∀ {C' X a : ℝ}, 0 < C' → C' ≤ max 1 (max C₁ C₂) → a ≤ C' * X →
      0 ≤ a → a ≤ max 1 (max C₁ C₂) * X := by
    intro C' X a hC' hle h ha
    have hX : 0 ≤ X := nonneg_of_mul_nonneg_right (ha.trans h) hC'
    exact h.trans (mul_le_mul_of_nonneg_right hle hX)
  refine ⟨max 1 (max C₁ C₂), le_max_left _ _, ?_, ?_⟩
  · intro u p f Ω I hΩ hI hsol x t ρ k c P F hρ hρ1 hwin hc hP hF β hβ i
    exact up hC₁ ((le_max_left _ _).trans (le_max_right _ _))
      (hvel u p f Ω I hΩ hI hsol x t ρ k c P F hρ hρ1 hwin hc hP hF β hβ i) (abs_nonneg _)
  · intro u p f Ω I hΩ hI hsol x t ρ k c Q F hρ hρ1 ht hball hc hQ hF β hβ
    exact up hC₂ ((le_max_right _ _).trans (le_max_right _ _))
      (hpres u p f Ω I hΩ hI hsol x t ρ k c Q F hρ hρ1 ht hball hc hQ hF β hβ) (abs_nonneg _)

end CIV
