/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularization

/-!
# Fixed-support jets of translated distribution kernels

The parameter derivative of `κ (y - z)` in directions `v i` is the spatial
iterated Fréchet derivative of `κ` in directions `-v i`.  Multiplication by a
fixed cutoff keeps every such jet in one compactly supported smooth-function
space.  This is the first finite-order input for differentiating a distribution
pairing with respect to its translation parameter.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending

/-- Evaluation at fixed directions as a continuous linear functional on the
space of continuous multilinear maps. -/
noncomputable def continuousMultilinearApplyCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} (v : Fin r → E) : (E [×r]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f v
      map_add' := fun f g ↦ by simp
      map_smul' := fun c f ↦ by simp }
    (∏ i, ‖v i‖) (fun f ↦ by
      dsimp
      simpa only [Real.norm_eq_abs, mul_comm] using f.le_opNorm v)

/-- The value of the `r`-th translation-parameter jet of
`y ↦ χ y * κ (y - z)` in the directions `v`. -/
noncomputable def cutoffTranslatedKernelJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (r : ℕ) (z y : E) (v : Fin r → E) : ℝ :=
  χ y * iteratedFDeriv ℝ r κ (y - z) (fun i ↦ -v i)

@[simp]
theorem cutoffTranslatedKernelJet_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (z y : E) (v : Fin 0 → E) :
    cutoffTranslatedKernelJet χ κ 0 z y v = χ y * κ (y - z) := by
  simp [cutoffTranslatedKernelJet]

/-- Smoothness of a fixed directional translation jet in the spatial
variable. -/
theorem cutoffTranslatedKernelJet_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (r : ℕ) (z : E) (v : Fin r → E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cutoffTranslatedKernelJet χ κ r z y v) := by
  rw [contDiff_infty]
  intro m
  have hχm : ContDiff ℝ m (χ : E → ℝ) :=
    χ.contDiff.of_le (by
      exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  apply hχm.mul
  have hderiv : ContDiff ℝ m (iteratedFDeriv ℝ r κ) :=
    hκ.iteratedFDeriv_right (by
      exact_mod_cast (show (m + r : ℕ∞) ≤ ⊤ from le_top))
  have htranslated : ContDiff ℝ m
      (fun y ↦ iteratedFDeriv ℝ r κ (y - z)) :=
    hderiv.comp (contDiff_id.sub contDiff_const)
  exact (continuousMultilinearApplyCLM (fun i ↦ -v i)).contDiff.comp htranslated

/-- A fixed directional translation jet, bundled in the common compact
support carried by the cutoff. -/
noncomputable def cutoffTranslatedKernelJetSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z : E) (v : Fin r → E) :
    ContDiffMapSupportedIn E ℝ ⊤ K :=
  .of_support_subset
    (cutoffTranslatedKernelJet_contDiff χ κ hκ r z v)
    (by
      change Function.support (fun y ↦ χ y *
        iteratedFDeriv ℝ r κ (y - z) (fun i ↦ -v i)) ⊆ K
      exact (Function.support_mul_subset_left _ _).trans
        ((subset_tsupport χ).trans hχK))

@[simp]
theorem cutoffTranslatedKernelJetSupportedIn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z y : E) (v : Fin r → E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z v y =
      χ y * iteratedFDeriv ℝ r κ (y - z) (fun i ↦ -v i) := by
  rfl

/-- The zeroth translation jet is the original fixed-support translated
kernel. -/
theorem cutoffTranslatedKernelJetSupportedIn_zero_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) (v : Fin 0 → E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK 0 z v =
      cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z := by
  ext y
  simp [cutoffTranslatedKernelJetSupportedIn_apply,
    cutoffTranslatedKernelSupportedIn_apply]

/-- Restriction of a distribution to one fixed-support smooth-function
space, kept as a continuous linear map for later finite-order estimates. -/
noncomputable def distributionOnSupportedInCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ContDiffMapSupportedIn E ℝ ⊤ K →L[ℝ] ℝ :=
  T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)

@[simp]
theorem distributionOnSupportedInCLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω)
    (φ : ContDiffMapSupportedIn E ℝ ⊤ K) :
    distributionOnSupportedInCLM T K hKΩ φ =
      T (TestFunction.ofSupportedIn hKΩ φ) :=
  rfl

/-- The candidate `r`-th parameter derivative of a distribution paired with
a cutoff-translated kernel, evaluated in fixed directions. -/
noncomputable def distributionCutoffTranslatedKernelJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) (v : Fin r → E) : ℝ :=
  distributionOnSupportedInCLM T K hKΩ
    (cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z v)

/-- At order zero the distributional jet is the original fixed-support
cutoff-translated pairing. -/
theorem distributionCutoffTranslatedKernelJet_zero_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z : E) (v : Fin 0 → E) :
    distributionCutoffTranslatedKernelJet T χ κ hκ K hχK hKΩ 0 z v =
      T (TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [distributionCutoffTranslatedKernelJet,
    distributionOnSupportedInCLM_apply,
    cutoffTranslatedKernelJetSupportedIn_zero_eq]

/-- Additivity of the fixed-support kernel jet in each direction slot. -/
theorem cutoffTranslatedKernelJetSupportedIn_update_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z : E)
    (v : Fin r → E) (i : Fin r) (x y : E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
        (Function.update v i (x + y)) =
      cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
          (Function.update v i x) +
        cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
          (Function.update v i y) := by
  ext q
  change χ q * iteratedFDeriv ℝ r κ (q - z)
      (fun j => -Function.update v i (x + y) j) =
    χ q * iteratedFDeriv ℝ r κ (q - z)
        (fun j => -Function.update v i x j) +
      χ q * iteratedFDeriv ℝ r κ (q - z)
        (fun j => -Function.update v i y j)
  let w : Fin r → E := fun j => -v j
  have hadd : (fun j => -Function.update v i (x + y) j) =
      Function.update w i ((-x) + (-y)) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji, add_comm]
  have hx : (fun j => -Function.update v i x j) =
      Function.update w i (-x) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  have hy : (fun j => -Function.update v i y j) =
      Function.update w i (-y) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  rw [hadd, hx, hy,
    (iteratedFDeriv ℝ r κ (q - z)).map_update_add]
  ring

/-- Homogeneity of the fixed-support kernel jet in each direction slot. -/
theorem cutoffTranslatedKernelJetSupportedIn_update_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z : E)
    (v : Fin r → E) (i : Fin r) (c : ℝ) (x : E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
        (Function.update v i (c • x)) =
      c • cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
          (Function.update v i x) := by
  ext q
  change χ q * iteratedFDeriv ℝ r κ (q - z)
      (fun j => -Function.update v i (c • x) j) =
    c * (χ q * iteratedFDeriv ℝ r κ (q - z)
      (fun j => -Function.update v i x j))
  let w : Fin r → E := fun j => -v j
  have hsmul : (fun j => -Function.update v i (c • x) j) =
      Function.update w i (c • (-x)) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  have hx : (fun j => -Function.update v i x j) =
      Function.update w i (-x) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  rw [hsmul, hx,
    (iteratedFDeriv ℝ r κ (q - z)).map_update_smul]
  ring

/-- The candidate distributional jet as an algebraic multilinear map of its
direction variables.  No continuity assertion is made at this layer. -/
noncomputable def distributionCutoffTranslatedKernelJetMultilinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin r => E) ℝ :=
  MultilinearMap.mk'
    (distributionCutoffTranslatedKernelJet T χ κ hκ K hχK hKΩ r z)
    (fun v i x y => by
      rw [distributionCutoffTranslatedKernelJet,
        cutoffTranslatedKernelJetSupportedIn_update_add,
        map_add]
      rfl)
    (fun v i c x => by
      rw [distributionCutoffTranslatedKernelJet,
        cutoffTranslatedKernelJetSupportedIn_update_smul,
        map_smul]
      rfl)

@[simp]
theorem distributionCutoffTranslatedKernelJetMultilinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) (v : Fin r → E) :
    distributionCutoffTranslatedKernelJetMultilinearMap
        T χ κ hκ K hχK hKΩ r z v =
      distributionCutoffTranslatedKernelJet
        T χ κ hκ K hχK hKΩ r z v := by
  rfl

/-- At order zero the algebraic multilinear package has the original
fixed-support distribution pairing as its unique value. -/
theorem distributionCutoffTranslatedKernelJetMultilinearMap_zero_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z : E) (v : Fin 0 → E) :
    distributionCutoffTranslatedKernelJetMultilinearMap
        T χ κ hκ K hχK hKΩ 0 z v =
      T (TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [distributionCutoffTranslatedKernelJetMultilinearMap_apply,
    distributionCutoffTranslatedKernelJet_zero_eq]

/-- Recursive finite-dimensional continuity upgrade for an algebraic
multilinear map, together with preservation of every pointwise value. -/
noncomputable def multilinearMapToContinuousOfFiniteDimensionalAux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∀ r : ℕ, (f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin r => E) ℝ) →
      {F : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ //
        ∀ v, F v = f v}
  | 0, f => by
      refine ⟨ContinuousMultilinearMap.uncurry0 ℝ E (f 0), ?_⟩
      intro v
      rw [ContinuousMultilinearMap.uncurry0_apply]
      congr 1
      funext i
      exact Fin.elim0 i
  | r + 1, f => by
      let L : E →ₗ[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
        { toFun := fun x =>
            (multilinearMapToContinuousOfFiniteDimensionalAux r
              (f.curryLeft x)).1
          map_add' := fun x y => by
            ext v
            change (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (x + y))).1 v =
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                  (f.curryLeft x)).1 v +
                (multilinearMapToContinuousOfFiniteDimensionalAux r
                  (f.curryLeft y)).1 v
            rw [(multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (x + y))).2 v,
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft x)).2 v,
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft y)).2 v]
            exact DFunLike.congr_fun ((f.curryLeft).map_add x y) v
          map_smul' := fun c x => by
            ext v
            change (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (c • x))).1 v =
              c • (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft x)).1 v
            rw [(multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (c • x))).2 v,
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft x)).2 v]
            exact DFunLike.congr_fun ((f.curryLeft).map_smul c x) v }
      refine ⟨(LinearMap.toContinuousLinearMap L).uncurryLeft, ?_⟩
      intro v
      rw [ContinuousLinearMap.uncurryLeft_apply]
      change (multilinearMapToContinuousOfFiniteDimensionalAux r
          (f.curryLeft (v 0))).1 (Fin.tail v) = f v
      rw [(multilinearMapToContinuousOfFiniteDimensionalAux r
          (f.curryLeft (v 0))).2 (Fin.tail v),
        MultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Every real multilinear map on finitely many copies of a
finite-dimensional normed space has its canonical pointwise-preserving
continuous upgrade. -/
noncomputable def multilinearMapToContinuousOfFiniteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ}
    (f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin r => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (multilinearMapToContinuousOfFiniteDimensionalAux r f).1

@[simp]
theorem multilinearMapToContinuousOfFiniteDimensional_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ}
    (f : MultilinearMap (RingHom.id ℝ) (fun _ : Fin r => E) ℝ) (v : Fin r → E) :
    multilinearMapToContinuousOfFiniteDimensional f v = f v :=
  (multilinearMapToContinuousOfFiniteDimensionalAux r f).2 v

/-- In finite-dimensional parameter spaces, the algebraic candidate
distributional jet is a continuous multilinear map in its direction
variables. -/
noncomputable def distributionCutoffTranslatedKernelJetContinuousMultilinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  multilinearMapToContinuousOfFiniteDimensional
    (distributionCutoffTranslatedKernelJetMultilinearMap
      T χ κ hκ K hχK hKΩ r z)

@[simp]
theorem distributionCutoffTranslatedKernelJetContinuousMultilinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) (v : Fin r → E) :
    distributionCutoffTranslatedKernelJetContinuousMultilinearMap
        T χ κ hκ K hχK hKΩ r z v =
      distributionCutoffTranslatedKernelJet
        T χ κ hκ K hχK hKΩ r z v := by
  rw [distributionCutoffTranslatedKernelJetContinuousMultilinearMap,
    multilinearMapToContinuousOfFiniteDimensional_apply,
    distributionCutoffTranslatedKernelJetMultilinearMap_apply]

/-- At order zero the continuous multilinear package has the original
fixed-support distribution pairing as its unique value. -/
theorem distributionCutoffTranslatedKernelJetContinuousMultilinearMap_zero_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z : E) (v : Fin 0 → E) :
    distributionCutoffTranslatedKernelJetContinuousMultilinearMap
        T χ κ hκ K hχK hKΩ 0 z v =
      T (TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [distributionCutoffTranslatedKernelJetContinuousMultilinearMap_apply,
    distributionCutoffTranslatedKernelJet_zero_eq]

end SGPT.Foundations.Analysis.Pending
