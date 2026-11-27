/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Existence

/-!
# Uniqueness of the free-field vacuum system (GNS uniqueness)

Any two vacuum Weyl systems `V : FreeFieldVacuum m H` and `V' : FreeFieldVacuum m H'` of the
same mass are unitarily equivalent: there is a surjective linear isometry `U : H ≃ₗᵢ[ℂ] H'`
with `U Ω = Ω'` and `U W(F) = W'(F) U` for every real test function `F`.

* `FreeFieldVacuum.weyl_zero`: `W(0) = 1`.
* `FreeFieldVacuum.inner_weyl_vacuum` (Gram formula):
  `⟪W(F)Ω, W(G)Ω⟫ = exp(i Im⟨κF, κ(G-F)⟩) · exp(-Re⟨κ(G-F), κ(G-F)⟩/2)`; the right side
  depends only on `m`, `F`, `G`.
* `FreeFieldVacuum.norm_linearCombination_eq`: `‖Σ c_F W'(F)Ω'‖ = ‖Σ c_F W(F)Ω‖`.
* `FreeFieldVacuum.intertwiner`: the linear isometry `H → H'` extending
  `Σ c_F W(F)Ω ↦ Σ c_F W'(F)Ω'` (by density of the span, `cyclic`).
* `FreeFieldVacuum.exists_unitary_equiv`: the unitary equivalence of the two systems.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate

namespace VacuumBellSeparation

/-! ### The one-particle data of the zero test function -/

theorem oneParticle_zero (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m 0 p = 0 := by
  have h : ∀ x : Spacetime, (((0 : RealTestFunction).1 x : ℝ) : ℂ) = 0 := fun x => by
    have h0 : (0 : RealTestFunction).1 x = 0 := rfl
    rw [h0, Complex.ofReal_zero]
  unfold oneParticle
  simp only [h, mul_zero, MeasureTheory.integral_zero]

theorem oneParticleInner_zero_zero (m : ℝ) : oneParticleInner m 0 0 = 0 := by
  unfold oneParticleInner
  simp only [oneParticle_zero, map_zero, zero_mul, MeasureTheory.integral_zero]

/-! ### Gram matrices of linear combinations -/

/-- Two families with the same Gram matrix have the same Gram matrix of linear combinations. -/
theorem inner_linearCombination_eq_of_inner_eq {ι E E' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (v : ι → E) (v' : ι → E') (h : ∀ i j, ⟪v i, v j⟫_ℂ = ⟪v' i, v' j⟫_ℂ) (c d : ι →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ v c, Finsupp.linearCombination ℂ v d⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ v' c, Finsupp.linearCombination ℂ v' d⟫_ℂ := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, inner_zero_left]
  | add c₁ c₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | single i a =>
    induction d using Finsupp.induction_linear with
    | zero => simp only [map_zero, inner_zero_right]
    | add d₁ d₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | single j b =>
      simp only [Finsupp.linearCombination_single, inner_smul_left, inner_smul_right, h]

variable {m : ℝ} {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

namespace FreeFieldVacuum

/-! ### Elementary consequences of the Weyl relations -/

/-- The Weyl operators preserve inner products. -/
theorem inner_weyl_weyl (V : FreeFieldVacuum m H) (F : RealTestFunction) (x y : H) :
    ⟪V.weyl F x, V.weyl F y⟫_ℂ = ⟪x, y⟫_ℂ :=
  ContinuousLinearMap.inner_map_map_of_mem_unitary (V.weyl_mem_unitary F) x y

/-- The Weyl relation applied to a vector: `W(F) W(G) x = e^{-i Im⟨κF, κG⟩} W(F + G) x`. -/
theorem weyl_apply_weyl (V : FreeFieldVacuum m H) (F G : RealTestFunction) (x : H) :
    V.weyl F (V.weyl G x) =
      Complex.exp (-(Complex.I * ((oneParticleInner m F G).im : ℂ))) • V.weyl (F + G) x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) (V.weyl_mul F G)
  first
  | exact h

/-- `W(0) = 1`. -/
theorem weyl_zero (V : FreeFieldVacuum m H) : V.weyl 0 = 1 := by
  have h : V.weyl 0 * V.weyl 0 = V.weyl 0 := by
    have h1 := V.weyl_mul 0 0
    have h2 : Complex.exp (-(Complex.I * ((oneParticleInner m 0 0).im : ℂ))) = 1 := by
      rw [oneParticleInner_zero_zero, Complex.zero_im, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.exp_zero]
    rw [h2, one_smul] at h1
    exact h1.trans (congrArg V.weyl (add_zero (0 : RealTestFunction)))
  have hs := Unitary.star_mul_self_of_mem (V.weyl_mem_unitary 0)
  calc V.weyl 0 = (star (V.weyl 0) * V.weyl 0) * V.weyl 0 := by rw [hs, one_mul]
    _ = star (V.weyl 0) * (V.weyl 0 * V.weyl 0) := mul_assoc _ _ _
    _ = 1 := by rw [h, hs]

theorem weyl_zero_apply (V : FreeFieldVacuum m H) (x : H) : V.weyl 0 x = x :=
  (congrArg (fun T : H →L[ℂ] H => T x) V.weyl_zero).trans rfl

/-! ### The Gram formula -/

/-- **Gram formula**: `⟪W(F)Ω, W(G)Ω⟫ = exp(i Im⟨κF, κ(G-F)⟩) · exp(-Re⟨κ(G-F), κ(G-F)⟩/2)`.
The right side depends only on `m`, `F` and `G`, not on the system. -/
theorem inner_weyl_vacuum (V : FreeFieldVacuum m H) (F G : RealTestFunction) :
    ⟪V.weyl F V.vacuum, V.weyl G V.vacuum⟫_ℂ =
      Complex.exp (Complex.I * ((oneParticleInner m F (G - F)).im : ℂ)) *
        ((Real.exp (-((oneParticleInner m (G - F) (G - F)).re / 2)) : ℝ) : ℂ) := by
  have h2 : V.weyl F (V.weyl (G - F) V.vacuum) =
      Complex.exp (-(Complex.I * ((oneParticleInner m F (G - F)).im : ℂ))) •
        V.weyl G V.vacuum := by
    rw [V.weyl_apply_weyl]
    exact congrArg (fun K => Complex.exp (-(Complex.I * ((oneParticleInner m F (G - F)).im : ℂ))) •
      V.weyl K V.vacuum) (add_sub_cancel F G)
  have h1 : ⟪V.weyl F V.vacuum, V.weyl F (V.weyl (G - F) V.vacuum)⟫_ℂ =
      ((Real.exp (-((oneParticleInner m (G - F) (G - F)).re / 2)) : ℝ) : ℂ) := by
    rw [V.inner_weyl_weyl, V.vacuum_weyl]
  rw [h2, inner_smul_right] at h1
  rw [← h1, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- The norms of linear combinations of the vectors `W(F)Ω` agree in any two systems. -/
theorem norm_linearCombination_eq (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H')
    (c : RealTestFunction →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (fun F => V'.weyl F V'.vacuum) c‖ =
      ‖Finsupp.linearCombination ℂ (fun F => V.weyl F V.vacuum) c‖ := by
  have h := inner_linearCombination_eq_of_inner_eq (fun F => V'.weyl F V'.vacuum)
    (fun F => V.weyl F V.vacuum)
    (fun F G => (V'.inner_weyl_vacuum F G).trans (V.inner_weyl_vacuum F G).symm) c c
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h]

/-! ### The intertwining isometry -/

/-- The vectors `W(F)Ω` span a dense subspace (cyclicity of the vacuum). -/
theorem denseRange_linearCombination (V : FreeFieldVacuum m H) :
    DenseRange (Finsupp.linearCombination ℂ (fun F => V.weyl F V.vacuum)) := by
  have hd : Dense ((Submodule.span ℂ (Set.range fun F => V.weyl F V.vacuum) : Submodule ℂ H) :
      Set H) := Submodule.dense_iff_topologicalClosure_eq_top.mpr V.cyclic
  refine Dense.mono ?_ hd
  intro x hx
  have hx' : x ∈ LinearMap.range (Finsupp.linearCombination ℂ (fun F => V.weyl F V.vacuum)) := by
    rw [Finsupp.range_linearCombination]
    exact hx
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hx'
  exact ⟨c, hc⟩

/-- The linear isometry `H → H'` extending `Σ c_F W(F)Ω ↦ Σ c_F W'(F)Ω'`. -/
noncomputable def intertwiner (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H') :
    H →ₗᵢ[ℂ] H' :=
  (Finsupp.linearCombination ℂ (fun F => V'.weyl F V'.vacuum)).extendOfIsometry
    V.denseRange_linearCombination (V.norm_linearCombination_eq V')

theorem intertwiner_linearCombination (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H')
    (c : RealTestFunction →₀ ℂ) :
    V.intertwiner V' (Finsupp.linearCombination ℂ (fun F => V.weyl F V.vacuum) c) =
      Finsupp.linearCombination ℂ (fun F => V'.weyl F V'.vacuum) c :=
  LinearMap.extendOfIsometry_eq (Finsupp.linearCombination ℂ (fun F => V'.weyl F V'.vacuum))
    V.denseRange_linearCombination (V.norm_linearCombination_eq V') c

theorem intertwiner_weyl_vacuum (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H')
    (F : RealTestFunction) :
    V.intertwiner V' (V.weyl F V.vacuum) = V'.weyl F V'.vacuum := by
  have h := V.intertwiner_linearCombination V' (Finsupp.single F 1)
  simp only [Finsupp.linearCombination_single, one_smul] at h
  exact h

/-- **Uniqueness of the vacuum representation** (GNS): two vacuum Weyl systems of the same
mass are unitarily equivalent, by a unitary mapping vacuum to vacuum and intertwining the
Weyl operators. -/
theorem exists_unitary_equiv (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H') :
    ∃ U : H ≃ₗᵢ[ℂ] H', U V.vacuum = V'.vacuum ∧ ∀ F x, U (V.weyl F x) = V'.weyl F (U x) := by
  have hsurj : Function.Surjective (V.intertwiner V') := by
    have hclosed : IsClosed (Set.range (V.intertwiner V')) :=
      (V.intertwiner V').isometry.isClosedEmbedding.isClosed_range
    have hsub : Set.range (Finsupp.linearCombination ℂ (fun F => V'.weyl F V'.vacuum)) ⊆
        Set.range (V.intertwiner V') := by
      rintro _ ⟨c, rfl⟩
      exact ⟨Finsupp.linearCombination ℂ (fun F => V.weyl F V.vacuum) c,
        V.intertwiner_linearCombination V' c⟩
    have h1 := closure_minimal hsub hclosed
    rw [V'.denseRange_linearCombination.closure_range] at h1
    intro y
    exact h1 (Set.mem_univ y)
  refine ⟨LinearIsometryEquiv.ofSurjective (V.intertwiner V') hsurj, ?_, ?_⟩
  · rw [LinearIsometryEquiv.coe_ofSurjective]
    calc V.intertwiner V' V.vacuum = V.intertwiner V' (V.weyl 0 V.vacuum) := by
          rw [V.weyl_zero_apply]
      _ = V'.weyl 0 V'.vacuum := V.intertwiner_weyl_vacuum V' 0
      _ = V'.vacuum := V'.weyl_zero_apply V'.vacuum
  · intro F x
    rw [LinearIsometryEquiv.coe_ofSurjective]
    have hext : (V.intertwiner V').toContinuousLinearMap.comp (V.weyl F) =
        (V'.weyl F).comp (V.intertwiner V').toContinuousLinearMap := by
      refine ContinuousLinearMap.ext_on
        (Submodule.dense_iff_topologicalClosure_eq_top.mpr V.cyclic) ?_
      rintro _ ⟨G, rfl⟩
      change V.intertwiner V' (V.weyl F (V.weyl G V.vacuum)) =
        V'.weyl F (V.intertwiner V' (V.weyl G V.vacuum))
      rw [V.weyl_apply_weyl, LinearIsometry.map_smul, V.intertwiner_weyl_vacuum,
        V.intertwiner_weyl_vacuum, V'.weyl_apply_weyl]
    exact DFunLike.congr_fun hext x

end FreeFieldVacuum

/-! ### Invariance of the vacuum Bell correlation under unitary equivalence -/

theorem mem_commutantOf_iff_of_starAlgEquiv (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H' →L[ℂ] H'))
    {S : Set (H →L[ℂ] H)} {S' : Set (H' →L[ℂ] H')} (hS : ∀ T, T ∈ S ↔ Φ T ∈ S')
    (T : H →L[ℂ] H) : T ∈ commutantOf S ↔ Φ T ∈ commutantOf S' := by
  have hstar : ∀ X : H →L[ℂ] H, Φ (star X) = star (Φ X) := fun X => Φ.map_star' X
  change T ∈ StarSubalgebra.centralizer ℂ S ↔ Φ T ∈ StarSubalgebra.centralizer ℂ S'
  rw [StarSubalgebra.mem_centralizer_iff, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h g' hg'
    have hg : Φ.symm g' ∈ S := (hS _).mpr (by rwa [StarAlgEquiv.apply_symm_apply])
    obtain ⟨h1, h2⟩ := h _ hg
    have e1 := congrArg (⇑Φ) h1
    have e2 := congrArg (⇑Φ) h2
    simp only [map_mul, hstar, StarAlgEquiv.apply_symm_apply] at e1 e2
    exact ⟨e1, e2⟩
  · intro h g hg
    obtain ⟨h1, h2⟩ := h (Φ g) ((hS g).mp hg)
    refine ⟨EquivLike.injective Φ ?_, EquivLike.injective Φ ?_⟩
    · simpa only [map_mul] using h1
    · simpa only [map_mul, hstar] using h2

theorem mem_generatedVNA_iff_of_starAlgEquiv (Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H' →L[ℂ] H'))
    {S : Set (H →L[ℂ] H)} {S' : Set (H' →L[ℂ] H')} (hS : ∀ T, T ∈ S ↔ Φ T ∈ S')
    (T : H →L[ℂ] H) : T ∈ generatedVNA S ↔ Φ T ∈ generatedVNA S' := by
  have hc := mem_commutantOf_iff_of_starAlgEquiv Φ hS
  change T ∈ (commutantOf S).commutant ↔ Φ T ∈ (commutantOf S').commutant
  rw [VonNeumannAlgebra.mem_commutant_iff, VonNeumannAlgebra.mem_commutant_iff]
  constructor
  · intro h g' hg'
    have hg : Φ.symm g' ∈ commutantOf S := (hc _).mpr (by rwa [StarAlgEquiv.apply_symm_apply])
    have e1 := congrArg (⇑Φ) (h _ hg)
    simp only [map_mul, StarAlgEquiv.apply_symm_apply] at e1
    exact e1
  · intro h g hg
    exact EquivLike.injective Φ (by simpa only [map_mul] using h (Φ g) ((hc g).mp hg))

theorem norm_conjStarAlgEquiv_le (U : H ≃ₗᵢ[ℂ] H') (A : H →L[ℂ] H) :
    ‖U.conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun y => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.norm_map]
  calc ‖A (U.symm y)‖ ≤ ‖A‖ * ‖U.symm y‖ := A.le_opNorm _
    _ = ‖A‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]

theorem mem_saContractions_iff_of_conj (U : H ≃ₗᵢ[ℂ] H') {M : VonNeumannAlgebra H}
    {M' : VonNeumannAlgebra H'} (hM : ∀ T, T ∈ M ↔ U.conjStarAlgEquiv T ∈ M')
    (A : H →L[ℂ] H) : A ∈ saContractions M ↔ U.conjStarAlgEquiv A ∈ saContractions M' := by
  constructor
  · rintro ⟨hA, hsa, hn⟩
    exact ⟨(hM A).mp hA, IsSelfAdjoint.map U.conjStarAlgEquiv hsa,
      (norm_conjStarAlgEquiv_le U A).trans hn⟩
  · rintro ⟨hA, hsa, hn⟩
    have e : U.conjStarAlgEquiv.symm (U.conjStarAlgEquiv A) = A :=
      StarAlgEquiv.symm_apply_apply _ A
    refine ⟨(hM A).mpr hA, ?_, ?_⟩
    · rw [← e]
      exact IsSelfAdjoint.map U.conjStarAlgEquiv.symm hsa
    · rw [← e]
      exact (norm_conjStarAlgEquiv_le U.symm _).trans hn

theorem conjStarAlgEquiv_chshOp (U : H ≃ₗᵢ[ℂ] H') (A₀ A₁ B₀ B₁ : H →L[ℂ] H) :
    U.conjStarAlgEquiv (chshOp A₀ A₁ B₀ B₁) =
      chshOp (U.conjStarAlgEquiv A₀) (U.conjStarAlgEquiv A₁) (U.conjStarAlgEquiv B₀)
        (U.conjStarAlgEquiv B₁) := by
  simp only [chshOp, map_add, map_mul, map_sub]

/-- The Bell correlation is invariant under a unitary equivalence of states and algebras. -/
theorem bellCorrelation_eq_of_conj (U : H ≃ₗᵢ[ℂ] H') (ω : State H) (ω' : State H')
    (hω : ∀ T, ω' (U.conjStarAlgEquiv T) = ω T) {𝔄 𝔅 : VonNeumannAlgebra H}
    {𝔄' 𝔅' : VonNeumannAlgebra H'} (h𝔄 : ∀ T, T ∈ 𝔄 ↔ U.conjStarAlgEquiv T ∈ 𝔄')
    (h𝔅 : ∀ T, T ∈ 𝔅 ↔ U.conjStarAlgEquiv T ∈ 𝔅') :
    bellCorrelation ω' 𝔄' 𝔅' = bellCorrelation ω 𝔄 𝔅 := by
  unfold bellCorrelation
  congr 1
  ext x
  constructor
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
    refine ⟨U.conjStarAlgEquiv.symm A₀, ?_, U.conjStarAlgEquiv.symm A₁, ?_,
      U.conjStarAlgEquiv.symm B₀, ?_, U.conjStarAlgEquiv.symm B₁, ?_, ?_⟩
    · rwa [mem_saContractions_iff_of_conj U h𝔄, StarAlgEquiv.apply_symm_apply]
    · rwa [mem_saContractions_iff_of_conj U h𝔄, StarAlgEquiv.apply_symm_apply]
    · rwa [mem_saContractions_iff_of_conj U h𝔅, StarAlgEquiv.apply_symm_apply]
    · rwa [mem_saContractions_iff_of_conj U h𝔅, StarAlgEquiv.apply_symm_apply]
    · rw [← hω, conjStarAlgEquiv_chshOp, StarAlgEquiv.apply_symm_apply,
        StarAlgEquiv.apply_symm_apply, StarAlgEquiv.apply_symm_apply,
        StarAlgEquiv.apply_symm_apply]
  · rintro ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
    refine ⟨U.conjStarAlgEquiv A₀, (mem_saContractions_iff_of_conj U h𝔄 A₀).mp hA₀,
      U.conjStarAlgEquiv A₁, (mem_saContractions_iff_of_conj U h𝔄 A₁).mp hA₁,
      U.conjStarAlgEquiv B₀, (mem_saContractions_iff_of_conj U h𝔅 B₀).mp hB₀,
      U.conjStarAlgEquiv B₁, (mem_saContractions_iff_of_conj U h𝔅 B₁).mp hB₁, ?_⟩
    rw [← conjStarAlgEquiv_chshOp, hω]

namespace FreeFieldVacuum

theorem conjStarAlgEquiv_weyl (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H')
    (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ F x, U (V.weyl F x) = V'.weyl F (U x)) (F : RealTestFunction) :
    U.conjStarAlgEquiv (V.weyl F) = V'.weyl F := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hU, LinearIsometryEquiv.apply_symm_apply]

theorem mem_localAlgebra_iff_of_conj (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H')
    (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ F x, U (V.weyl F x) = V'.weyl F (U x)) (O : Set Spacetime)
    (T : H →L[ℂ] H) : T ∈ localAlgebra V O ↔ U.conjStarAlgEquiv T ∈ localAlgebra V' O := by
  refine mem_generatedVNA_iff_of_starAlgEquiv U.conjStarAlgEquiv (fun X => ?_) T
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, conjStarAlgEquiv_weyl V V' U hU F⟩
  · rintro ⟨F, hF, hX⟩
    refine ⟨F, hF, EquivLike.injective U.conjStarAlgEquiv ?_⟩
    rw [hX, conjStarAlgEquiv_weyl V V' U hU F]

theorem vectorState_conj (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H')
    (U : H ≃ₗᵢ[ℂ] H') (hΩ : U V.vacuum = V'.vacuum) (T : H →L[ℂ] H) :
    vectorState V'.vacuum V'.vacuum_norm (U.conjStarAlgEquiv T) =
      vectorState V.vacuum V.vacuum_norm T := by
  change ⟪V'.vacuum, U.conjStarAlgEquiv T V'.vacuum⟫_ℂ = ⟪V.vacuum, T V.vacuum⟫_ℂ
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, ← hΩ,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

/-- The vacuum Bell correlation `β_m(R, L)` does not depend on the choice of the vacuum Weyl
system of mass `m`. -/
theorem freeFieldBell_eq (V : FreeFieldVacuum m H) (V' : FreeFieldVacuum m H') (R L : ℝ) :
    freeFieldBell V R L = freeFieldBell V' R L := by
  obtain ⟨U, hΩ, hU⟩ := V.exists_unitary_equiv V'
  symm
  exact bellCorrelation_eq_of_conj U _ _ (vectorState_conj V V' U hΩ)
    (mem_localAlgebra_iff_of_conj V V' U hU _) (mem_localAlgebra_iff_of_conj V V' U hU _)

end FreeFieldVacuum

end VacuumBellSeparation
