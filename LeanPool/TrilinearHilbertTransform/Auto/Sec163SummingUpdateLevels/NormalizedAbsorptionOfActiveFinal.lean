/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec163SummingUpdateLevels.Setup

/-!
# Trilinear Hilbert transform: normalizedAbsorption_of_activeFinal
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def NormalizedAbsorptionOfActiveFinalStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (Cc : ℕ)
    (Aa : ℕ)
    (θ₀ : ℝ)
    (c' : ℕ)
    (Cb : ℕ)
    (_ : (2 : ℕ) ≤ Aa)
    (_ : (1 : ℕ) ≤ c')
    (q : ℝ)
    (cs : ℝ)
    (Cfin : ℝ)
    (_ : (0 : ℝ) ≤ Cfin)
    (K : ℕ)
    (_ : ∀ (k : ℕ), K ≤ k → ∀ (N : ℕ) (d₀ : ℤ) (B : ActiveSetup κ c'), (∀ I ∈ B.cells, B.w I
      ≠ (0 : ℝ × ℝ → ℂ) → d₀ ≤ I.1 ∧ I.1 < d₀ + (↑N : ℤ)) → B.LevelProps k Cb (Real.exp
      ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)) → ∑ I ∈ B.cells, dyadicGridLength B.G I.1 * ‖B.Hf I
      (B.Y I)‖ ≤ (Cfin * Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀) ^ cs * ((1 : ℝ) +
      finiteDepthConstant κ q N) + Real.exp (-(↑k : ℝ))) * dyadicGridLength B.G B.R.1)
    (Ct : ℕ)
    (Ca : ℕ)
    (Cr : ℝ)
    (_ : ∀ {ι : Type} [Fintype ι] (B : ι → ActiveSetup κ c') {E η₀ X W : ℝ}, (1 : ℝ) ≤ E → (0
      : ℝ) ≤ η₀ → (0 : ℝ) ≤ X → (∀ (p : ι), (1 : ℝ) ≤ (B p).H ∧ (B p).H ≤ E ∧ (B p).Dc ≤
      E ∧ (↑(Fintype.card (B p).L) : ℝ) ≤ E ∧ (B p).S = (2 : ℝ) ∧ (B p).η = (4 : ℝ) * η₀
      ∧ ∑ I ∈ (B p).cells, dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).z (3 : Fin
      (4 : ℕ)) I)‖ ≤ η₀ * (X * dyadicGridLength (B p).G (B p).R.1)) → ∑ p : ι,
      dyadicGridLength (B p).G (B p).R.1 ≤ W → ∑ p : ι, ∑ I ∈ (B p).cells,
      dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).Y I)‖ ≤ W * (η₀ * X + (3 : ℝ) *
      ((4 : ℝ) * η₀) * ((4 : ℝ) * E ^ (3 : ℕ) * ((↑Ca : ℝ) * ((216 : ℝ) * ((100 : ℝ) *
      ((1 : ℝ) + Real.log E) ^ (3 : ℕ)) + Real.log (sliceConst κ) + (2 : ℝ) * Real.log
      (2 : ℝ)) ^ Ca)) + (3 : ℝ) * E ^ (3 : ℕ) * (E ^ (3 : ℕ) * ((2 : ℝ) + E * E)) * ((1
      / 2 : ℝ) * Cr * ((100 : ℝ) * ((1 : ℝ) + Real.log E) ^ (3 : ℕ) + Real.log (2 : ℝ) +
      (1 : ℝ)) ^ Ct)))
    (c : ℝ)
    (Cq : ℝ)
    (K₁ : ℕ)
    (_ : ∀ (k₁ : ℕ), K₁ ≤ k₁ → ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (w : ℤ × ℤ → ℝ × ℝ
      → ℂ), (∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I)) → ∀ (f : Fin (4 : ℕ) → ℝ → ℂ), (∀ (p : Fin (4 :
      ℕ)), Measurable (f p)) → (∀ (p : Fin (4 : ℕ)), ∀ I ∈ dyadicFiniteTree G J N, I = J
      ∨ kernelHull G J N w I → eLpNorm (f p) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      (1 : ℝ≥0∞)) → ∃ (M : ℕ → ℕ) (roots : ℕ → Finset (ℤ × ℤ)) (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
      (n : ℕ → ℤ × ℤ → ℕ) (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ) (g : ℕ → ℤ × ℤ → ℝ → ℂ) (cnt : ℕ →
      ℤ × ℤ → ℤ × ℤ → ℕ) (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ), (∀ (t : ℕ),
      IsAdaptiveFit c₂ (fitBudget Cq Cc (stagAcc k₁ Aa t)) G J N w (stagPos t) q (f
      (stagPos t)) (stagAcc k₁ Aa t) (M t) (roots t) (seg t) (n t) (a t) (g t) ∧
      IsAttemptData c₂ (fitBudget Cq Cc (stagAcc k₁ Aa t)) G J N (M t) (roots t) (seg t)
      (n t) (a t) (cnt t) (atm t) ∧ IsFitOpponent G J N (f (stagPos t)) (roots t) (seg
      t) (g t) (fitOpponentConst (M t)) (max (2 : ℝ) (↑(M t) : ℝ)) c₂ (fitBudget Cq Cc
      (stagAcc k₁ Aa t))) ∧ (∀ (L : Finset ℕ), dyadicRootLength G (L.biUnion roots) ≤
      (↑L.card : ℝ) * ((4 / 3 : ℝ) * dyadicGridLength G J.1)) ∧ (∀ I ∈ dyadicFiniteTree
      G J N, kernelHull G J N w I → ∃ (D : StaggerCell κ), D.a₀ = dyadicGridLeft G I.1
      I.2 ∧ D.r = dyadicGridLength G I.1 ∧ D.w = w I ∧ D.q = q ∧ D.f = f ∧ (∀ (t : ℕ),
      D.g t = g t I) ∧ (∀ (t : ℕ), D.k t = (↑(stagAcc k₁ Aa t) : ℝ)) ∧ (∀ (u t : ℕ), (12
      : ℕ) ≤ t → (1 : ℕ) ≤ u → u < t → stagPos u ≠ stagPos t → ∀ (s s' : Fin (4 : ℕ)), s
      ≠ s' → PairSmall D.a₀ D.r D.w s s' (D.tuple u t s) (D.tuple u t s') (Real.exp ((-2
      : ℝ) * (↑(stagAcc k₁ Aa t) : ℝ) ^ θ₀))) ∧ (∀ (T : ℕ), D.H D.f = D.H (D.tail T) + ∑
      u ∈ Finset.Icc (1 : ℕ) T, (D.H (Function.update (D.tail T) (stagPos u) (D.incr u))
      + ∑ t ∈ Finset.Ioc u T, if stagPos t ≠ stagPos u then D.H (D.tuple u t) else (0 :
      ℂ))) ∧ (∀ (T : ℕ), (4 : ℕ) ≤ T → ‖D.H (D.tail T)‖ ≤ (32 : ℝ) * Real.exp
      (-(↑(stagAcc k₁ Aa (T - (3 : ℕ))) : ℝ)) ∧ ∀ (u : ℕ), ‖D.H (Function.update (D.tail
      T) (stagPos u) (D.incr u))‖ ≤ (32 : ℝ) * Real.exp (-(↑(stagAcc k₁ Aa (T - (3 :
      ℕ))) : ℝ))) ∧ ∀ (u t : ℕ) (l : Fin (4 : ℕ)), eLpNorm (D.tuple u t l) (2 : ℝ≥0∞)
      D.μ ≤ (2 : ℝ≥0∞)) ∧ ∀ (u t : ℕ), (1 : ℕ) ≤ u → u < t → stagPos u ≠ stagPos t → ∀
      (η₀ : ℝ), Real.exp ((-2 : ℝ) * (↑(stagAcc k₁ Aa t) : ℝ) ^ θ₀) ≤ η₀ → (∀ I ∈
      dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (s s' : Fin (4 : ℕ)), s ≠ s' →
      PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      (stagTuple f g u t I s) (stagTuple f g u t I s') η₀) → ∃ (ι : Type) (_ : Fintype
      ι) (B : ι → ActiveSetup κ c'), ∑ p : ι, dyadicGridLength G (B p).R.1 ≤ (91 / 3 :
      ℝ) * dyadicGridLength G J.1 ∧ (∀ (p p' : ι), ∀ I ∈ (B p).cells, I ∈ (B p').cells →
      p = p') ∧ (∀ (p : ι), (B p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (B p).cells,
      kernelHull G J N w I) ∧ (∀ I ∈ (B p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G
      (B p).R.1 (B p).R.2 → J' ∈ (B p).cells) ∧ (B p).G = G ∧ (B p).w = w ∧ (B p).R ∈
      dyadicFiniteTree G J N ∧ (1 : ℝ) ≤ (B p).H ∧ (B p).H ≤ Real.exp ((↑(stagAcc k₁ Aa
      t) : ℝ) ^ Cb) ∧ (B p).Dc ≤ Real.exp ((↑(stagAcc k₁ Aa t) : ℝ) ^ Cb) ∧
      (↑(Fintype.card (B p).L) : ℝ) ≤ Real.exp ((↑(stagAcc k₁ Aa t) : ℝ) ^ Cb) ∧ (B p).S
      = (2 : ℝ) ∧ (B p).η = (4 : ℝ) * η₀ ∧ (∀ I ∈ (B p).cells, ∀ (s s' : Fin (4 : ℕ)), s
      ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      ((B p).Y I s) ((B p).Y I s') ((2 : ℝ) * η₀)) ∧ (∀ I ∈ (B p).cells, ∀ (l : Fin (4 :
      ℕ)), (eLpNorm ((B p).Y I l) (2 : ℝ≥0∞) ((B p).μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l :
      Fin (4 : ℕ)), ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * (eLpNorm ((B p).U l I)
      (2 : ℝ≥0∞) ((B p).μ I)).toReal ^ (2 : ℕ) ≤ (↑(stagAcc k₁ Aa t) : ℝ) ^ Cb *
      dyadicGridLength G (B p).R.1) ∧ ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B
      p).Hf I ((B p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑(stagAcc k₁ Aa t) : ℝ) ^ Cb *
      dyadicGridLength G (B p).R.1) ∧ (B p).HasColumnRep (1 : ℝ) ∧ (B p).SubRootProps η₀
      ((↑(stagAcc k₁ Aa t) : ℝ) ^ Cb)) ∧ ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength
      G I.1 * ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t
      I)‖ ≤ ∑ p : ι, ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B p).Hf I ((B p).Y
      I)‖ + Real.exp (-(↑(stagAcc k₁ Aa t) : ℝ)) * ((91 / 3 : ℝ) * dyadicGridLength G
      J.1))
    (K₃ : ℕ)
    (K₄ : ℕ),
  let k₁ : ℕ :=
    max (max K₁ K) (max K₃ (max K₄ (2 : ℕ)))
  ∀ (_ : K₁ ≤ k₁)
    (_ : K ≤ k₁)
    (_ : (2 : ℕ) ≤ k₁),
  let kk : ℕ → ℕ :=
    fun (t : ℕ) => stagAcc k₁ Aa t
  ∀ (_ : ∀ (t : ℕ), k₁ ≤ kk t),
  let E : ℕ → ℝ :=
    fun (t : ℕ) => Real.exp ((↑(kk t) : ℝ) ^ Cb)
  let η₁ : ℕ → ℝ :=
    fun (t : ℕ) => max (Real.exp ((-2 : ℝ) * (↑(kk t) : ℝ) ^ θ₀)) ((4 : ℝ) *
      localFormUniformConstant κ)
  let Φ : ℕ → ℝ :=
    fun (t : ℕ) => η₁ t * (↑(kk t) : ℝ) ^ Cb + (3 : ℝ) * ((4 : ℝ) * η₁ t) * ((4 : ℝ) * E
      t ^ (3 : ℕ) * ((↑Ca : ℝ) * ((216 : ℝ) * ((100 : ℝ) * ((1 : ℝ) + Real.log (E t)) ^
      (3 : ℕ)) + Real.log (sliceConst κ) + (2 : ℝ) * Real.log (2 : ℝ)) ^ Ca)) + (3 : ℝ)
      * E t ^ (3 : ℕ) * (E t ^ (3 : ℕ) * ((2 : ℝ) + E t * E t)) * ((1 / 2 : ℝ) * Cr *
      ((100 : ℝ) * ((1 : ℝ) + Real.log (E t)) ^ (3 : ℕ) + Real.log (2 : ℝ) + (1 : ℝ)) ^
      Ct)
  let Init : ℕ → ℝ :=
    fun (t : ℕ) => (91 / 3 : ℝ) * Φ t + Real.exp (-(↑(kk t) : ℝ)) * (91 / 3 : ℝ)
  ∀ (_ : Init = fun (t : ℕ) => (91 / 3 : ℝ) * Φ t + Real.exp (-(↑(kk t) : ℝ)) * (91 / 3 : ℝ))
    (_ : ∀ (t : ℕ), (1 : ℝ) ≤ E t)
    (_ : ∀ (t : ℕ), (0 : ℝ) ≤ η₁ t)
    (_ : ∀ (t : ℕ), (0 : ℝ) ≤ Init t),
  let A₀c : ℝ :=
    ∑ t ∈ Finset.range (12 : ℕ), Init t
  ∀ (_ : (0 : ℝ) ≤ A₀c),
  let bn : ℕ → ℝ :=
    fun (t : ℕ) => (91 / 3 : ℝ) * (Cfin * Real.exp (-((2 : ℝ) * cs) * (↑(kk t) : ℝ) ^
      θ₀) + Real.exp (-(↑(kk t) : ℝ))) + Real.exp (-(↑(kk t) : ℝ)) * (91 / 3 : ℝ)
  ∀ (_ : bn = fun (t : ℕ) => (91 / 3 : ℝ) * (Cfin * Real.exp (-((2 : ℝ) * cs) * (↑(kk t) : ℝ)
      ^ θ₀) + Real.exp (-(↑(kk t) : ℝ))) + Real.exp (-(↑(kk t) : ℝ)) * (91 / 3 : ℝ)),
  let bc : ℕ → ℝ :=
    fun (t : ℕ) => (91 / 3 : ℝ) * Cfin * Real.exp (-((2 : ℝ) * cs) * (↑(kk t) : ℝ) ^ θ₀)
  ∀ (_ : bc = fun (t : ℕ) => (91 / 3 : ℝ) * Cfin * Real.exp (-((2 : ℝ) * cs) * (↑(kk t) : ℝ)
      ^ θ₀))
    (_ : ∀ (t : ℕ), (0 : ℝ) ≤ bn t)
    (_ : ∀ (t : ℕ), (0 : ℝ) ≤ bc t)
    (_ : Summable fun (t : ℕ) => (↑t : ℝ) * bn t)
    (_ : Summable fun (t : ℕ) => (↑t : ℝ) * bc t)
    (_ : ∑' (t : ℕ), (↑t : ℝ) * bc t ≤ c),
  let A : ℝ :=
    (55 : ℝ) * A₀c + ∑' (t : ℕ), (↑t : ℝ) * bn t
  ∀ (_ : A = (55 : ℝ) * A₀c + ∑' (t : ℕ), (↑t : ℝ) * bn t)
    (N : ℕ)
    (D : FiniteDepthLocalData κ q N)
    (root : ℤ × ℤ),
  let G : RealDyadicGrid :=
    D.grid
  ∀ (_ : ∀ I ∈ D.cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G root.1 root.2),
  let f : Fin (4 : ℕ) → ℝ → ℂ :=
    D.input
  ∀ (_ : ∀ K ∈ dyadicHullCells G D.cells root, ∀ (j : Fin (4 : ℕ)), cellLqNorm G q (f j) K ≤
      (1 : ℝ≥0∞))
    (_ : (1 : ℝ) ≤ finiteDepthConstant κ q N)
    (_ : (0 : ℝ) ≤ dyadicGridLength G root.1)
    (I₀ : ℤ × ℤ)
    (_ : I₀ ∈ D.cells),
  finiteDepthNumerator D ≤ (A + c * finiteDepthConstant κ q N) * dyadicGridLength G
    root.1




private theorem normalizedAbsorption_of_activeFinal_stage_1 :
  NormalizedAbsorptionOfActiveFinalStage1Statement := by
  classical
  intro κ c₂ Cc Aa θ₀ c' Cb hAa hc' q cs Cfin hCfin K hK Ct Ca Cr htot c Cq K₁ hstep K₃ K₄ k₁
    hk₁K₁ hk₁K hk₁2 kk hkk E η₁ Φ Init hInit_def hE1 hη₁0 hInit0 A₀c hA₀c bn hbn_def bc hbc_def
    hbn0 hbc0 hsum_bn hsum_bc htsum_bc A hA_def N D root G hsub f hnorm hCN1 hroot0 I₀ hI₀
  set! N' : ℕ := (D.firstDepth + N - root.1).toNat with hN'_def
  have hmemT : ∀ I ∈ D.cells, I ∈ dyadicFiniteTree G root N' := fun I hI => by
    refine (dyadicFiniteTree_mem_iff G root I N').mpr ⟨hsub I hI, ?_⟩
    have h1 := (D.depths I hI).2
    have h2 := dyadicGridCell_depth_le_of_subset G I root (hsub I hI)
    omega
  set! w : ℤ × ℤ → ℝ × ℝ → ℂ := fun I => if I ∈ D.cells then D.kernel I else 0 with hw_def
  have hw : ∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
      (w I) := fun I => by
    by_cases hI : I ∈ D.cells
    · simp only [hw_def, hI, ↓reduceIte]; exact D.admissible I hI
    · simp only [hw_def, hI, ↓reduceIte]
      exact isAdmissibleLocalKernel_zero κ _ (dyadicGridLength_pos G I.1)
  have hwne : ∀ I, w I ≠ 0 → I ∈ D.cells := fun I h => by
    by_contra hI; exact h (by simp [hw_def, hI])
  have hfq : ∀ p, ∀ I ∈ dyadicFiniteTree G root N', (I = root ∨ kernelHull G root N' w I) →
      eLpNorm (f p) (ENNReal.ofReal q)
        (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1 := by
    intro p I hI hIH
    have hIr := ((dyadicFiniteTree_mem_iff G root I N').mp hI).1
    have hhull : I ∈ dyadicHullCells G D.cells root := by
      refine ⟨hIr, ?_⟩
      rcases hIH with rfl | ⟨c₀', -, hc₀', hwc⟩
      · exact ⟨I₀, hI₀, hsub I₀ hI₀⟩
      · exact ⟨c₀', hwne c₀' hwc, hc₀'⟩
    exact hnorm I hhull p
  obtain ⟨M, roots, seg, n, a, g, cnt, atm, hfit, hroots, hcells, hlev⟩ :=
    hstep k₁ hk₁K₁ G root N' w hw f D.measurable_input hfq
  -- the numerator as a tree sum
  have hnum : finiteDepthNumerator D = ∑ I ∈ dyadicFiniteTree G root N', dyadicGridLength G I.1 *
      ‖localProgressionForm (dyadicGridLength G I.1) (w I) f‖ := by
    unfold finiteDepthNumerator
    rw [← Finset.sum_subset (fun I hI => hmemT I hI) (fun I _ hI => by
      simp [hw_def, hI, localProgressionForm_zero_kernel])]
    refine Finset.sum_congr rfl fun I hI => ?_
    simp only [hw_def, hI, ↓reduceIte]
    rfl
  set! JJ := dyadicGridLength G root.1 with hJJ
  rewrite [← hJJ] at hroot0 hroots hlev ⊢
  set! CN := finiteDepthConstant κ q N with hCN_def
  rewrite [← hCN_def] at hCN1 ⊢
  have hJJ0 : 0 ≤ JJ := hroot0
  -- the initial levels
  have hinit : ∀ u t, t < 12 → levelSum G root N' w f g u t ≤ A₀c * JJ := by
    intro u t ht
    unfold levelSum
    split_ifs with hv
    swap
    · exact mul_nonneg hA₀c hJJ0
    obtain ⟨hu, hut, hpos⟩ := hv
    have hpair : ∀ I ∈ dyadicFiniteTree G root N', kernelHull G root N' w I → ∀ s s' : Fin 4,
        s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
          (stagTuple f g u t I s) (stagTuple f g u t I s') (η₁ t) := by
      intro I hI hIH s s' hss
      obtain ⟨Dc, ha₀, hr, -, -, hfD, hgD, -, -, -, -, hszD⟩ := hcells I hI hIH
      have hT := StaggerCell.tuple_eq_stagTuple Dc hfD hgD u t
      have hsz : ∀ l, eLpNorm (stagTuple f g u t I l) 2
          (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 2 := by
        intro l
        have := hszD u t l
        rw [hT] at this
        change eLpNorm _ 2 (normalizedIntervalMeasure Dc.a₀ Dc.r) ≤ 2 at this
        rwa [ha₀, hr] at this
      have hm : ∀ l, Measurable (stagTuple f g u t I l) := fun l => by
        rw [← hT]; exact Dc.tuple_measurable u t l
      exact (pairSmall_trivial (dyadicGridLength_pos G I.1) (hw I) hss (hm s) (hm s') (hsz s)
        (hsz s')).mono (le_max_right _ _)
    obtain ⟨ι, hι, B, hpack, -, hB, hsum⟩ :=
      hlev u t hu hut (Ne.symm hpos) (η₁ t) (le_max_left _ _) hpair
    have hB' : ∀ p, 1 ≤ (B p).H ∧ (B p).H ≤ E t ∧ (B p).Dc ≤ E t ∧
        (Fintype.card (B p).L : ℝ) ≤ E t ∧ (B p).S = 2 ∧ (B p).η = 4 * η₁ t ∧
        ∑ I ∈ (B p).cells, dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).z 3 I)‖ ≤
          η₁ t * ((kk t : ℝ) ^ Cb * dyadicGridLength (B p).G (B p).R.1) := fun p => by
      obtain ⟨-, -, -, hG', -, -, hH1, hHE, hDc, hL, hS, hη, -, -, -, htwo, -⟩ := hB p
      rw [hG']
      exact ⟨hH1, hHE, hDc, hL, hS, hη, htwo⟩
    have hW : ∑ p, dyadicGridLength (B p).G (B p).R.1 ≤ 91 / 3 * JJ := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) hpack
      rw [(hB p).2.2.2.1]
    have h := htot B (hE1 t) (hη₁0 t) (by positivity) hB' hW
    have hconv : ∑ p, ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B p).Hf I ((B p).Y I)‖ =
        ∑ p, ∑ I ∈ (B p).cells, dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).Y I)‖ :=
      Finset.sum_congr rfl fun p _ => by rw [(hB p).2.2.2.1]
    rw [hconv] at hsum
    have hle : Init t ≤ A₀c := Finset.single_le_sum (fun t _ => hInit0 t)
      (Finset.mem_range.mpr ht)
    calc _ ≤ _ := hsum
      _ ≤ 91 / 3 * JJ * Φ t + Real.exp (-(kk t : ℝ)) * (91 / 3 * JJ) := by
          gcongr
      _ = Init t * JJ := by simp only [hInit_def]; ring
      _ ≤ A₀c * JJ := mul_le_mul_of_nonneg_right hle hJJ0
  -- the later levels
  have hlate : ∀ u t, 12 ≤ t → u < t → levelSum G root N' w f g u t ≤
      JJ * (bn t + CN * bc t) := by
    intro u t ht _
    unfold levelSum
    split_ifs with hv
    swap
    · have := hbn0 t; have := hbc0 t; positivity
    obtain ⟨hu, hut, hpos⟩ := hv
    set! η := Real.exp (-2 * (kk t : ℝ) ^ θ₀) with hη_def
    have hpair : ∀ I ∈ dyadicFiniteTree G root N', kernelHull G root N' w I → ∀ s s' : Fin 4,
        s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
          (stagTuple f g u t I s) (stagTuple f g u t I s') η := by
      intro I hI hIH s s' hss
      obtain ⟨Dc, ha₀, hr, hwD, -, hfD, hgD, -, hpairD, -, -, -⟩ := hcells I hI hIH
      have := hpairD u t ht hu hut (Ne.symm hpos) s s' hss
      rw [StaggerCell.tuple_eq_stagTuple Dc hfD hgD, ha₀, hr, hwD] at this
      exact this
    obtain ⟨ι, hι, B, hpack, -, hB, hsum⟩ := hlev u t hu hut (Ne.symm hpos) η le_rfl hpair
    have hp : ∀ p, ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B p).Hf I ((B p).Y I)‖ ≤
        (Cfin * η ^ cs * (1 + CN) + Real.exp (-(kk t : ℝ))) * dyadicGridLength G (B p).R.1 := by
      intro p
      obtain ⟨-, -, hanc, hG', hw', -, hH1, hHE, hDc, hL, hS, hη', hpairs, hsize, hside, htwo,
        hcol⟩ := hB p
      have hwin : ∀ I ∈ (B p).cells, (B p).w I ≠ 0 →
          D.firstDepth ≤ I.1 ∧ I.1 < D.firstDepth + N := fun I _ hI => by
        rw [hw'] at hI
        exact D.depths I (hwne I hI)
      have hprops : (B p).LevelProps (kk t) Cb η := by
        unfold ActiveSetup.LevelProps
        rw [hG', hw']
        exact ⟨hanc, hH1, hHE, hDc, hL, hS, hη', hpairs, hsize, hside, htwo, hcol⟩
      have h := hK (kk t) (le_trans hk₁K (hkk t)) N D.firstDepth (B p) hwin hprops
      rw [hG'] at h
      exact h
    have hcoef0 : 0 ≤ Cfin * η ^ cs * (1 + CN) + Real.exp (-(kk t : ℝ)) := by positivity
    have hsetups : ∑ p, ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B p).Hf I ((B p).Y I)‖ ≤
        (Cfin * η ^ cs * (1 + CN) + Real.exp (-(kk t : ℝ))) * (91 / 3 * JJ) := by
      calc _ ≤ ∑ p, (Cfin * η ^ cs * (1 + CN) + Real.exp (-(kk t : ℝ))) *
            dyadicGridLength G (B p).R.1 := Finset.sum_le_sum fun p _ => hp p
        _ = (Cfin * η ^ cs * (1 + CN) + Real.exp (-(kk t : ℝ))) *
            ∑ p, dyadicGridLength G (B p).R.1 := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hpack hcoef0
    have hηcs : η ^ cs = Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀) := by
      rw [hη_def, ← Real.exp_mul]; ring_nf
    calc _ ≤ _ := hsum
      _ ≤ (Cfin * η ^ cs * (1 + CN) + Real.exp (-(kk t : ℝ))) * (91 / 3 * JJ) +
          Real.exp (-(kk t : ℝ)) * (91 / 3 * JJ) := by
          gcongr
      _ = JJ * (bn t + CN * bc t) := by
          rw [hηcs]; simp only [hbn_def, hbc_def]; ring
  -- the cutoff remainders
  set! S0 := ∑ I ∈ dyadicFiniteTree G root N', dyadicGridLength G I.1 with hS0_def
  set! X := ∑ I ∈ dyadicFiniteTree G root N', dyadicGridLength G I.1 *
      ‖localProgressionForm (dyadicGridLength G I.1) (w I) f‖ with hX_def
  rewrite [← hX_def] at hnum
  set! Er : ℕ → ℝ := fun T => if 4 ≤ T then ((T : ℝ) + 1) * (32 * Real.exp (-(kk (T - 3) : ℝ))) * S0
    else X with hEr_def
  have hkkt : ∀ t : ℕ, 1 ≤ t → (t : ℝ) ≤ kk t := fun t ht => by
    have h1 := le_stagAcc_pow (k₁ := k₁) (A := Aa) (by omega) hAa ht
    have h2 : t < 2 ^ t := Nat.lt_two_pow_self
    have h3 : 2 ^ t ≤ k₁ ^ t := Nat.pow_le_pow_left hk₁2 t
    exact_mod_cast (h2.le.trans (h3.trans h1))
  have hEr : Filter.Tendsto Er Filter.atTop (nhds 0) := by
    refine (tendsto_cutoff_remainder hkkt S0).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 4] with T hT
    simp only [hEr_def, hT, ↓reduceIte]
  have hXT : ∀ T, X ≤ Er T + ∑ u ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Ioc u T,
      levelSum G root N' w f g u t := by
    intro T
    by_cases hT : 4 ≤ T
    · simp only [hEr_def, hT, ↓reduceIte]
      rw [← sum_levelSum]
      exact tree_expansion_bound (kk := kk) (fun I hI hIH => by
        obtain ⟨Dc, -, hr, hwD, -, hfD, hgD, -, -, hexp, hbd, -⟩ := hcells I hI hIH
        exact ⟨Dc, hr, hwD, hfD, hgD, hexp, hbd⟩) T hT
    · simp only [hEr_def, hT, ↓reduceIte]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun t _ =>
        levelSum_nonneg _ _ _ _ _ _ _ _)
  -- the summation over the levels
  have hb0 : ∀ t, 0 ≤ JJ * (bn t + CN * bc t) := fun t => by
    have := hbn0 t; have := hbc0 t; positivity
  have hbsum : Summable fun t : ℕ => (t : ℝ) * (JJ * (bn t + CN * bc t)) := by
    have := (hsum_bn.mul_left JJ).add (hsum_bc.mul_left (JJ * CN))
    refine this.congr fun t => ?_
    ring
  have hfinal := levels_cutoff_sum Er hEr (levelSum G root N' w f g)
    (fun u t => levelSum_nonneg _ _ _ _ _ _ _ _) hXT hinit (fun t => JJ * (bn t + CN * bc t)) hb0
    hlate hbsum
  have htsum : ∑' t : ℕ, (t : ℝ) * (JJ * (bn t + CN * bc t)) =
      JJ * ∑' t : ℕ, (t : ℝ) * bn t + JJ * CN * ∑' t : ℕ, (t : ℝ) * bc t := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hsum_bn.mul_left _)
      (hsum_bc.mul_left _)]
    exact tsum_congr fun t => by ring
  rw [hnum]
  change X ≤ (A + c * CN) * JJ
  rw [htsum] at hfinal
  have hc' : JJ * CN * ∑' t : ℕ, (t : ℝ) * bc t ≤ JJ * CN * c :=
    mul_le_mul_of_nonneg_left htsum_bc (by positivity)
  calc X ≤ 55 * (A₀c * JJ) + (JJ * ∑' t : ℕ, (t : ℝ) * bn t +
        JJ * CN * ∑' t : ℕ, (t : ℝ) * bc t) := hfinal
    _ ≤ 55 * (A₀c * JJ) + (JJ * ∑' t : ℕ, (t : ℝ) * bn t + JJ * CN * c) := by linarith only [hc']
    _ = (A + c * CN) * JJ := by simp only [hA_def]; ring


open Classical in
/-- Blueprint prop:normalized (lines 2827-2904) from `eq:active-final`: the base reduction
(`activeCellReduction`, every level), the depth-independent initial levels
(`setups_total_le`), the active-final bound for the later levels, the level sums
(`update_levels_sum`) and the cutoff limit (`levels_cutoff_sum`) give `eq:normalized` with an
arbitrarily small coefficient of `C_N`. -/
theorem normalizedAbsorption_of_activeFinal (κ : LocalKernelClass) (hAF : ActiveFinal κ) :
    ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∀ c : ℝ, 0 < c → ∃ A : ℝ, 0 ≤ A ∧
      ∀ N, NormalizedAbsorption κ q N A c := by
  obtain ⟨c₂, Cc, Aa, θ₀, c', Cb, hc₂, hCc, hAa, hθ₀, hθ₁, hc', hred⟩ := activeCellReduction κ
  obtain ⟨q, hq2, hq3, cs, Cfin, hcs, hCfin, K, hK⟩ := hAF c' Cb θ₀ hc' hθ₀ hθ₁
  obtain ⟨Ct, Ca, Cr, hCr, htot⟩ := setups_total_le κ c' hc'
  refine ⟨q, hq2, hq3, fun c hc => ?_⟩
  obtain ⟨Cq, K₁, hCq, hstep⟩ := hred q hq2
  set! Λ : ℝ := 91 / 3 * Cfin + 1 with hΛ_def
  have hΛ : 0 < Λ := by positivity
  obtain ⟨K₃, hK₃⟩ := update_levels_sum (c := 2 * cs) (by positivity) hθ₀ hAa
    (ε := c / Λ) (by positivity)
  obtain ⟨K₄, hK₄⟩ := update_levels_sum (c := 1) one_pos hθ₀ hAa (ε := 1) one_pos
  set! k₁ := max (max K₁ K) (max K₃ (max K₄ 2)) with hk₁_def
  have hk₁K₁ : K₁ ≤ k₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk₁K : K ≤ k₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk₁K₃ : K₃ ≤ k₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hk₁K₄ : K₄ ≤ k₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)
  have hk₁2 : 2 ≤ k₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)
  set! kk : ℕ → ℕ := fun t => stagAcc k₁ Aa t with hkk_def
  have hkk : ∀ t, k₁ ≤ kk t := fun t => le_stagAcc (by omega) (by omega) t
  have hkk1 : ∀ t, (1 : ℝ) ≤ kk t := fun t => by exact_mod_cast le_trans (by omega) (hkk t)
  -- the level constants
  set! E : ℕ → ℝ := fun t => Real.exp ((kk t : ℝ) ^ Cb) with hE_def
  set! η₁ : ℕ → ℝ := fun t =>
    max (Real.exp (-2 * (kk t : ℝ) ^ θ₀)) (4 * localFormUniformConstant κ) with hη₁_def
  set! Φ : ℕ → ℝ := fun t => η₁ t * ((kk t : ℝ) ^ Cb) + 3 * (4 * η₁ t) * (4 * E t ^ 3 *
      (Ca * (216 * (100 * (1 + Real.log (E t)) ^ 3) + Real.log (sliceConst κ) +
        2 * Real.log 2) ^ Ca)) +
      3 * E t ^ 3 * (E t ^ 3 * (2 + E t * E t)) *
        (1 / 2 * Cr * (100 * (1 + Real.log (E t)) ^ 3 + Real.log 2 + 1) ^ Ct) with hΦ_def
  set! Init : ℕ → ℝ := fun t => 91 / 3 * Φ t + Real.exp (-(kk t : ℝ)) * (91 / 3) with hInit_def
  have hE1 : ∀ t, 1 ≤ E t := fun t => Real.one_le_exp (by positivity)
  have hη₁0 : ∀ t, 0 ≤ η₁ t := fun t => le_trans (Real.exp_pos _).le (le_max_left _ _)
  have hΦ0 : ∀ t, 0 ≤ Φ t := by
    intro t
    have := hE1 t
    have hl : 0 ≤ Real.log (E t) := Real.log_nonneg this
    have hls : 0 ≤ Real.log (sliceConst κ) := Real.log_nonneg (one_le_sliceConst κ)
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have := hη₁0 t
    simp only [hΦ_def]
    positivity
  have hInit0 : ∀ t, 0 ≤ Init t := fun t => by
    have := hΦ0 t; have := hη₁0 t; simp only [hInit_def]; positivity
  set! A₀c : ℝ := ∑ t ∈ Finset.range 12, Init t with hA₀c_def
  have hA₀c : 0 ≤ A₀c := Finset.sum_nonneg fun t _ => hInit0 t
  set! bn : ℕ → ℝ := fun t => 91 / 3 * (Cfin * Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀) +
      Real.exp (-(kk t : ℝ))) + Real.exp (-(kk t : ℝ)) * (91 / 3) with hbn_def
  set! bc : ℕ → ℝ := fun t => 91 / 3 * Cfin * Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀) with hbc_def
  have hbn0 : ∀ t, 0 ≤ bn t := fun t => by simp only [hbn_def]; positivity
  have hbc0 : ∀ t, 0 ≤ bc t := fun t => by simp only [hbc_def]; positivity
  -- summability of the later levels
  obtain ⟨hs3, hs3'⟩ := hK₃ k₁ hk₁K₃
  obtain ⟨hs4, -⟩ := hK₄ k₁ hk₁K₄
  have hexpk : ∀ t, Real.exp (-(kk t : ℝ)) ≤ Real.exp (-1 * (kk t : ℝ) ^ θ₀) := fun t => by
    rw [Real.exp_le_exp]
    have : (kk t : ℝ) ^ θ₀ ≤ (kk t : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (hkk1 t) hθ₁
      rwa [Real.rpow_one] at this
    linarith only [this]
  have hbn_le : ∀ t : ℕ, (t : ℝ) * bn t ≤ 91 / 3 * Cfin * (((t : ℝ) + 1) *
      Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀)) +
      182 / 3 * (((t : ℝ) + 1) * Real.exp (-1 * (kk t : ℝ) ^ θ₀)) := fun t => by
    have h1 := hexpk t
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have he := (Real.exp_pos (-(2 * cs) * (kk t : ℝ) ^ θ₀)).le
    have he' := (Real.exp_pos (-1 * (kk t : ℝ) ^ θ₀)).le
    simp only [hbn_def]
    nlinarith only [mul_le_mul_of_nonneg_left h1 ht0, mul_nonneg ht0 he, mul_nonneg hCfin he, he']
  have hsum_bn : Summable fun t : ℕ => (t : ℝ) * bn t :=
    Summable.of_nonneg_of_le (fun t => mul_nonneg (Nat.cast_nonneg t) (hbn0 t)) hbn_le
      ((hs3.mul_left _).add (hs4.mul_left _))
  have hbc_le : ∀ t : ℕ, (t : ℝ) * bc t ≤ 91 / 3 * Cfin * (((t : ℝ) + 1) *
      Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀)) := fun t => by
    simp only [hbc_def]
    have := (Real.exp_pos (-(2 * cs) * (kk t : ℝ) ^ θ₀)).le
    nlinarith only [mul_nonneg hCfin this]
  have hsum_bc : Summable fun t : ℕ => (t : ℝ) * bc t :=
    Summable.of_nonneg_of_le (fun t => mul_nonneg (Nat.cast_nonneg t) (hbc0 t)) hbc_le
      (hs3.mul_left _)
  have htsum_bc : ∑' t : ℕ, (t : ℝ) * bc t ≤ c := by
    calc ∑' t : ℕ, (t : ℝ) * bc t ≤ ∑' t : ℕ, 91 / 3 * Cfin * (((t : ℝ) + 1) *
          Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀)) :=
          hsum_bc.tsum_le_tsum hbc_le (hs3.mul_left _)
      _ = 91 / 3 * Cfin * ∑' t : ℕ, ((t : ℝ) + 1) * Real.exp (-(2 * cs) * (kk t : ℝ) ^ θ₀) :=
          tsum_mul_left
      _ ≤ 91 / 3 * Cfin * (c / Λ) := mul_le_mul_of_nonneg_left hs3' (by positivity)
      _ ≤ c := by
          rw [mul_div, div_le_iff₀ hΛ]
          nlinarith only [hc, hΛ_def]
  set! A : ℝ := 55 * A₀c + ∑' t : ℕ, (t : ℝ) * bn t with hA_def
  have hA0 : 0 ≤ A := add_nonneg (by positivity)
    (tsum_nonneg fun t => mul_nonneg (Nat.cast_nonneg t) (hbn0 t))
  refine ⟨A, hA0, fun N => ?_⟩
  intro D root hsub hnorm
  set! G := D.grid with hG_def
  rewrite [← hG_def] at hsub hnorm ⊢
  set! f := D.input with hf_def
  rewrite [← hf_def] at hnorm
  have hCN1 : 1 ≤ finiteDepthConstant κ q N := (finiteDepthConstant_bounds κ hq2.le N).1
  have hroot0 := (dyadicGridLength_pos G root.1).le
  -- the empty collection
  by_cases hDe : D.cells = ∅
  · unfold finiteDepthNumerator
    rw [hDe, Finset.sum_empty]
    exact mul_nonneg (by nlinarith only [hc, hA0, hCN1]) hroot0
  obtain ⟨I₀, hI₀⟩ := Finset.nonempty_iff_ne_empty.mpr hDe
  -- the finite tree below the root containing the used cells
  expose_names
  exact @normalizedAbsorption_of_activeFinal_stage_1 κ c₂ Cc Aa θ₀ c' Cb hAa hc' q cs Cfin hCfin K
    hK Ct Ca Cr htot c Cq K₁ hstep K₃ K₄ hk₁K₁ hk₁K hk₁2 hkk hInit_def hE1 hη₁0 hInit0 hA₀c
    hbn_def hbc_def hbn0 hbc0 hsum_bn hsum_bc htsum_bc hA_def N D root hsub hnorm hCN1 hroot0 I₀
    hI₀

/-- Blueprint thm:uniform-local from `eq:active-final`: every admissible class has `q ∈ (2, 3)`
with `sup_N C_N(q) < ∞`. -/
theorem uniform_of_activeFinal (hAF : ∀ κ : LocalKernelClass, ActiveFinal κ) :
    ∀ κ : LocalKernelClass, ∃ q, 2 ≤ q ∧ q < 3 ∧ ∃ Cst : ℝ,
      ∀ N, finiteDepthConstant κ q N ≤ Cst := by
  refine uniform_of_normalized fun κ => ?_
  obtain ⟨q, hq2, hq3, h⟩ := normalizedAbsorption_of_activeFinal κ (hAF κ)
  have hK : 0 < 4 / 3 * (16 : ℝ) ^ (4 / q) := by positivity
  obtain ⟨A, hA, hN⟩ := h (1 / 2 / (4 / 3 * (16 : ℝ) ^ (4 / q))) (by positivity)
  refine ⟨q, hq2.le, hq3, A, _, hA, by positivity, ?_, hN⟩
  rw [mul_div_cancel₀ _ hK.ne']

/-- Blueprint thm:main from `eq:active-final` for every admissible class: the trilinear Hilbert
transform principal value is bounded `L³ × L³ × L³ → L¹` on Schwartz functions and extends
uniquely. -/
theorem tht_main_of_activeFinal (hAF : ∀ κ : LocalKernelClass, ActiveFinal κ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ,
        (∀ x, Filter.Tendsto (TrilinearHT.truncatedTransform ![⇑f₁, ⇑f₂, ⇑f₃] x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃] x))) ∧
        MemLp (TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) 1 volume ∧
        ∫⁻ x, ‖TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃] x‖ₑ ≤
          ENNReal.ofReal C * (eLpNorm f₁ 3 volume * eLpNorm f₂ 3 volume * eLpNorm f₃ 3 volume)) ∧
      ∃ T' : Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 3 (volume : Measure ℝ) →L[ℂ]
          Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ),
        (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ, ⇑(T' (f₁.toLp 3 (volume : Measure ℝ))
          (f₂.toLp 3 (volume : Measure ℝ)) (f₃.toLp 3 (volume : Measure ℝ))) =ᵐ[volume]
            TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) ∧
        (∀ x y z, ‖T' x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) ∧
        ∀ S : Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 3 (volume : Measure ℝ) →L[ℂ]
            Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ),
          (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ, ⇑(S (f₁.toLp 3 (volume : Measure ℝ))
            (f₂.toLp 3 (volume : Measure ℝ)) (f₃.toLp 3 (volume : Measure ℝ))) =ᵐ[volume]
              TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) → S = T' :=
  tht_main_of_uniform (uniform_of_activeFinal hAF)

open Classical in
/-- Blueprint `eq:active-min` and `eq:active-final` (prop:base line 1622, prop:normalized lines
2885-2888) on the active cells: for every pattern with at least three basic arguments, the
weighted minima over the cells active at `δ_k = e^{-k^{C_b+2}}` are at most
`C η₀^{c_*} (1 + C_N) |R|`. -/
def ActiveMin (κ : LocalKernelClass) : Prop :=
  ∀ (c' Cb : ℕ) (θ₀ : ℝ), 1 ≤ c' → 0 < θ₀ → θ₀ ≤ 1 → ∃ q : ℝ, 2 < q ∧ q < 3 ∧
    ∃ cs Cfin : ℝ, 0 < cs ∧ 0 ≤ Cfin ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (N : ℕ) (d₀ : ℤ)
      (B : ActiveSetup κ c'), (∀ I ∈ B.cells, B.w I ≠ 0 → d₀ ≤ I.1 ∧ I.1 < d₀ + N) →
      B.LevelProps k Cb (Real.exp (-2 * (k : ℝ) ^ θ₀)) → ∀ p : Fin 3,
      ∑ I ∈ B.cells with B.active (Real.exp (-(k : ℝ) ^ (Cb + 2))) I,
          dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z (Fin.castSucc p) I)‖ ≤
        Cfin * Real.exp (-2 * (k : ℝ) ^ θ₀) ^ cs * (1 + finiteDepthConstant κ q N) *
          dyadicGridLength B.G B.R.1

/-- The inactive error of the base reduction at `δ_k = e^{-k^{C_b+2}}` is eventually at most
`e^{-k}` per unit length, uniformly over setups with budgets `exp(k^{C_b})`. -/
theorem inactive_error_small (Cb C : ℕ) (Cr : ℝ) (hCr : 0 ≤ Cr) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ {H Dc Lc : ℝ}, 1 ≤ H → H ≤ Real.exp ((k : ℝ) ^ Cb) →
      0 ≤ Dc → Dc ≤ Real.exp ((k : ℝ) ^ Cb) → 0 ≤ Lc → Lc ≤ Real.exp ((k : ℝ) ^ Cb) →
      3 * Lc ^ 3 * (Dc ^ 3 * (2 + Lc * Dc)) *
        (Real.exp (-(k : ℝ) ^ (Cb + 2)) * Cr * (Real.log (chartTranslationBudget H) +
          Real.log (Real.exp (-(k : ℝ) ^ (Cb + 2)))⁻¹ + 1) ^ C) ≤ Real.exp (-(k : ℝ)) := by
  have hev := ev_mul_pow_le_exp ((Cr + 1) * 802 ^ C) (C * (3 * Cb + 2))
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 13 ⌈L₀⌉₊, fun k hk H Dc Lc hH1 hHE hDc0 hDcE hL0 hLE => ?_⟩
  set x : ℝ := (k : ℝ) with hx
  have hx13 : (13 : ℝ) ≤ x := by
    have : 13 ≤ k := le_trans (le_max_left _ _) hk
    rw [hx]; exact_mod_cast this
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx13]
  have hkL : ⌈L₀⌉₊ ≤ k := le_trans (le_max_right _ _) hk
  have hxL : L₀ ≤ x := (Nat.le_ceil L₀).trans (by rw [hx]; exact_mod_cast hkL)
  set E := Real.exp (x ^ Cb) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  -- the budget factor
  have hfac : 3 * Lc ^ 3 * (Dc ^ 3 * (2 + Lc * Dc)) ≤ 9 * E ^ 8 := by
    have h1 : Lc ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ hL0 hLE 3
    have h2 : Dc ^ 3 ≤ E ^ 3 := pow_le_pow_left₀ hDc0 hDcE 3
    have h3 : Lc * Dc ≤ E * E := mul_le_mul hLE hDcE hDc0 (by linarith only [hE1])
    have hE2 : (1 : ℝ) ≤ E * E := by nlinarith only [hE1]
    calc 3 * Lc ^ 3 * (Dc ^ 3 * (2 + Lc * Dc)) ≤ 3 * E ^ 3 * (E ^ 3 * (2 + E * E)) := by
          gcongr
      _ ≤ 3 * E ^ 3 * (E ^ 3 * (3 * (E * E))) := by gcongr; linarith only [hE2]
      _ = 9 * E ^ 8 := by ring
  -- the logarithmic factor
  have hlogH : Real.log (chartTranslationBudget H) ≤ 100 * (1 + x ^ Cb) ^ 3 := by
    have := (log_chartTranslationBudget_le hH1 hHE).2
    rwa [Real.log_exp] at this
  have hlog0 : 0 ≤ Real.log (chartTranslationBudget H) :=
    (log_chartTranslationBudget_le hH1 hHE).1
  have hlogδ : Real.log (Real.exp (-x ^ (Cb + 2)))⁻¹ = x ^ (Cb + 2) := by
    rw [Real.log_inv, Real.log_exp, neg_neg]
  have hxp : ∀ n : ℕ, 1 ≤ x ^ n := fun n => one_le_pow₀ hx1
  have hpoly : Real.log (chartTranslationBudget H) + Real.log (Real.exp (-x ^ (Cb + 2)))⁻¹ + 1 ≤
      802 * x ^ (3 * Cb + 2) := by
    rw [hlogδ]
    have h1 : (1 + x ^ Cb) ^ 3 ≤ 8 * x ^ (3 * Cb) := by
      have : 1 + x ^ Cb ≤ 2 * x ^ Cb := by linarith only [hxp Cb]
      calc (1 + x ^ Cb) ^ 3 ≤ (2 * x ^ Cb) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = 8 * x ^ (3 * Cb) := by rw [mul_pow, ← pow_mul]; ring_nf
    have h2 : x ^ (3 * Cb) ≤ x ^ (3 * Cb + 2) := pow_le_pow_right₀ hx1 (by omega)
    have h3 : x ^ (Cb + 2) ≤ x ^ (3 * Cb + 2) := pow_le_pow_right₀ hx1 (by omega)
    have h4 := hxp (3 * Cb + 2)
    nlinarith only [hlogH, h1, h2, h3, h4]
  have hpow : (Real.log (chartTranslationBudget H) + Real.log (Real.exp (-x ^ (Cb + 2)))⁻¹ + 1) ^
      C ≤ 802 ^ C * x ^ (C * (3 * Cb + 2)) := by
    calc _ ≤ (802 * x ^ (3 * Cb + 2)) ^ C := pow_le_pow_left₀ (by
          rw [hlogδ]; have := hxp (Cb + 2); linarith only [hlog0, this]) hpoly C
      _ = 802 ^ C * x ^ (C * (3 * Cb + 2)) := by rw [mul_pow, ← pow_mul, mul_comm (3 * Cb + 2)]
  have hpexp : Cr * (802 ^ C * x ^ (C * (3 * Cb + 2))) ≤ Real.exp x := by
    have := hL₀ x hxL
    have hc : Cr * (802 ^ C * x ^ (C * (3 * Cb + 2))) ≤
        (Cr + 1) * 802 ^ C * x ^ (C * (3 * Cb + 2)) := by
      have : 0 ≤ 802 ^ C * x ^ (C * (3 * Cb + 2)) := by positivity
      nlinarith only [this]
    linarith only [this, hc]
  -- the exponent comparison
  have hexpo : 8 * x ^ Cb + x + Real.log 9 + x ≤ x ^ (Cb + 2) := by
    have hl9 : Real.log 9 ≤ 8 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 by norm_num); linarith only [this]
    have h1 : x ^ (Cb + 2) = x ^ Cb * x * x := by ring
    have h2 := hxp Cb
    have hx0 : (0 : ℝ) ≤ x := by linarith only [hx]
    have hc1 : x ^ Cb * 13 ≤ x ^ Cb * x := mul_le_mul_of_nonneg_left hx13 (by positivity)
    have hc2 : x ^ Cb * x * 13 ≤ x ^ Cb * x * x :=
      mul_le_mul_of_nonneg_left hx13 (by positivity)
    have hc3 : 1 * x ≤ x ^ Cb * x := mul_le_mul_of_nonneg_right h2 hx0
    have hA : 169 * x ^ Cb ≤ x ^ Cb * x * x := by linarith only [hc1, hc2]
    have hB : 13 * x ≤ x ^ Cb * x * x := by linarith only [hc2, hc3]
    rw [h1]; linarith only [hx13, hl9, hc1, hc2, hc3]
  have hpos9 : (0 : ℝ) < 9 := by norm_num
  calc 3 * Lc ^ 3 * (Dc ^ 3 * (2 + Lc * Dc)) *
        (Real.exp (-x ^ (Cb + 2)) * Cr * (Real.log (chartTranslationBudget H) +
          Real.log (Real.exp (-x ^ (Cb + 2)))⁻¹ + 1) ^ C)
      ≤ 9 * E ^ 8 * (Real.exp (-x ^ (Cb + 2)) * (Cr * (802 ^ C * x ^ (C * (3 * Cb + 2))))) := by
        have h0 : 0 ≤ Real.exp (-x ^ (Cb + 2)) * Cr * (Real.log (chartTranslationBudget H) +
            Real.log (Real.exp (-x ^ (Cb + 2)))⁻¹ + 1) ^ C := by
          rw [hlogδ]; positivity
        refine (mul_le_mul_of_nonneg_right hfac h0).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCr) (by positivity)
    _ ≤ 9 * E ^ 8 * (Real.exp (-x ^ (Cb + 2)) * Real.exp x) := by gcongr
    _ = Real.exp (Real.log 9 + 8 * x ^ Cb - x ^ (Cb + 2) + x) := by
        rw [hE, ← Real.exp_nat_mul, Real.exp_add, Real.exp_sub, Real.exp_add,
          Real.exp_log hpos9, Real.exp_neg]
        push_cast; ring
    _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith only [hexpo])

/-- Blueprint prop:base (lines 1655-1660) with `eq:active-final`: the active-cell minima of the
three patterns, the two-`U` term `η₀ k^{C_b} |R|` and the inactive error `e^{-k} |R|` give the
active-final bound for the whole setup. -/
theorem activeFinal_of_activeMin {κ : LocalKernelClass} (hAM : ActiveMin κ) : ActiveFinal κ := by
  classical
  intro c' Cb θ₀ hc' hθ₀ hθ₁
  obtain ⟨q, hq2, hq3, cs, Cfin, hcs, hCfin, K, hK⟩ := hAM c' Cb θ₀ hc' hθ₀ hθ₁
  obtain ⟨Cred, Crr, hCrr, hred⟩ := ActiveSetup.reduction κ c' hc'
  obtain ⟨Kin, hKin⟩ := inactive_error_small Cb Cred Crr hCrr
  obtain ⟨K₂, hK₂⟩ := eventually_pow_mul_exp_le Cb hθ₀
  refine ⟨q, hq2, hq3, min cs (1 / 2), 3 * Cfin + 1, lt_min hcs (by norm_num), by positivity,
    max K (max Kin (max K₂ 1)), fun k hk N d₀ B hwin hprops => ?_⟩
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hkKin : Kin ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkK₂ : K₂ ≤ k := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hk
  set η := Real.exp (-2 * (k : ℝ) ^ θ₀) with hη_def
  set! δ := Real.exp (-(k : ℝ) ^ (Cb + 2)) with hδ_def
  set CN := finiteDepthConstant κ q N with hCN_def
  have hCN : 1 ≤ CN := (finiteDepthConstant_bounds κ hq2.le N).1
  have hR0 := (dyadicGridLength_pos B.G B.R.1).le
  have hprops' := hprops
  obtain ⟨-, hH1, hHE, hDc, hL, hS, hηB, -, -, -, htwo, -⟩ := hprops'
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (k : ℝ) ^ θ₀ := by positivity
    linarith only [this])
  have h := hred B δ (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by
    have : 0 ≤ (k : ℝ) ^ (Cb + 2) := by positivity
    linarith only [this])) (by rw [hηB]; positivity)
  -- the active minima
  have hact : ∑ p : Fin 3, ∑ I ∈ B.cells with B.active δ I,
      dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z (Fin.castSucc p) I)‖ ≤
        3 * (Cfin * η ^ cs * (1 + CN) * dyadicGridLength B.G B.R.1) := by
    refine (Finset.sum_le_sum fun p _ => hK k hkK N d₀ B hwin hprops p).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  -- the two-U term
  have htwo' : ∑ I ∈ B.cells, dyadicGridLength B.G I.1 * ‖B.Hf I (B.z 3 I)‖ ≤
      η ^ (1 / 2 : ℝ) * dyadicGridLength B.G B.R.1 := by
    refine htwo.trans ?_
    have h1 := hK₂ k hkK₂
    have h2 : η ^ (1 / 2 : ℝ) = Real.exp (-(k : ℝ) ^ θ₀) := by
      rw [hη_def, ← Real.exp_mul]; ring_nf
    rw [h2, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hR0
    linarith only [mul_comm η ((k : ℝ) ^ Cb), h1]
  -- the inactive error
  have hin := hKin k hkKin hH1 hHE B.Dc_nonneg hDc (Nat.cast_nonneg _) hL
  rw [hS] at h
  have hinact : 3 * (Fintype.card B.L : ℝ) ^ 3 * (B.Dc ^ 3 * (2 + Fintype.card B.L * B.Dc)) *
      (dyadicGridLength B.G B.R.1 *
        (δ * Crr * (Real.log (chartTranslationBudget B.H) + Real.log δ⁻¹ + 1) ^ Cred)) ≤
      Real.exp (-(k : ℝ)) * dyadicGridLength B.G B.R.1 := by
    have e : 3 * (Fintype.card B.L : ℝ) ^ 3 * (B.Dc ^ 3 * (2 + Fintype.card B.L * B.Dc)) *
        (dyadicGridLength B.G B.R.1 *
          (δ * Crr * (Real.log (chartTranslationBudget B.H) + Real.log δ⁻¹ + 1) ^ Cred)) =
        3 * (Fintype.card B.L : ℝ) ^ 3 * (B.Dc ^ 3 * (2 + Fintype.card B.L * B.Dc)) *
          (δ * Crr * (Real.log (chartTranslationBudget B.H) + Real.log δ⁻¹ + 1) ^ Cred) *
          dyadicGridLength B.G B.R.1 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hin hR0
  -- the exponents
  set cs' := min cs (1 / 2 : ℝ)
  have hcs1 : η ^ cs ≤ η ^ cs' :=
    Real.rpow_le_rpow_of_exponent_ge (Real.exp_pos _) hη1 (min_le_left _ _)
  have hcs2 : η ^ (1 / 2 : ℝ) ≤ η ^ cs' :=
    Real.rpow_le_rpow_of_exponent_ge (Real.exp_pos _) hη1 (min_le_right _ _)
  have hηcs : 0 ≤ η ^ cs' := Real.rpow_nonneg hη0 _
  have hηcs0 : 0 ≤ η ^ cs := Real.rpow_nonneg hη0 _
  calc ∑ I ∈ B.cells, dyadicGridLength B.G I.1 * ‖B.Hf I (B.Y I)‖
      ≤ 3 * (Cfin * η ^ cs * (1 + CN) * dyadicGridLength B.G B.R.1) +
          η ^ (1 / 2 : ℝ) * dyadicGridLength B.G B.R.1 +
          Real.exp (-(k : ℝ)) * dyadicGridLength B.G B.R.1 := by linarith only [h, hact, htwo',
              hinact]
    _ ≤ ((3 * Cfin + 1) * η ^ cs' * (1 + CN) + Real.exp (-(k : ℝ))) *
          dyadicGridLength B.G B.R.1 := by
        have k1 : 3 * (Cfin * η ^ cs * (1 + CN)) ≤ 3 * Cfin * η ^ cs' * (1 + CN) := by
          have := mul_le_mul_of_nonneg_left hcs1 hCfin
          nlinarith only [hCN, this]
        have k2 : η ^ (1 / 2 : ℝ) ≤ η ^ cs' * (1 + CN) := by nlinarith only [hCN, hcs2, hηcs]
        nlinarith only [hR0, k1, k2]

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)
variable (R' : ℤ × ℤ)

open Classical in
/-- Blueprint prop:normalized, lines 2840-2842 ("at each such root restart on the original base
summands ... their normalized sizes and rolling bounds hold there"): the level properties pass to
the cells below every dyadic sub-root of the root. -/
theorem LevelProps.below {k Cb : ℕ} {η₀ : ℝ} (h : A.LevelProps k Cb η₀)
    (hR' : dyadicGridCell A.G R'.1 R'.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) :
    (A.below R').LevelProps k Cb η₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, -, h13⟩ := h
  obtain ⟨hs, ht, hc⟩ := h13 R' hR'
  refine ⟨fun I hI J' hIJ hJR => ?_, h2, h3, h4, h5, h6, h7,
    fun I hI => h8 I (Finset.mem_filter.mp hI).1, fun I hI => h9 I (Finset.mem_filter.mp hI).1,
    hs, ht, ?_, fun R'' hR'' => ?_⟩
  · have hI' := Finset.mem_filter.mp hI
    exact Finset.mem_filter.mpr ⟨h1 I hI'.1 J' hIJ (hJR.trans hR'), hJR⟩
  · intro l
    obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := hc l
    exact ⟨P₁, P₂, h₁, h₂, c₁.mono (fun I hI => Finset.mem_filter.mp hI) le_rfl le_rfl,
      c₂.mono (fun I hI => Finset.mem_filter.mp hI) le_rfl le_rfl,
      e₁.mono (fun I hI => Finset.mem_filter.mp hI), e₂.mono (fun I hI => Finset.mem_filter.mp hI),
      fun I hI => hP I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2⟩
  · change dyadicGridCell A.G R''.1 R''.2 ⊆ dyadicGridCell A.G R'.1 R'.2 at hR''
    obtain ⟨hs', ht', hc'⟩ := h13 R'' (hR''.trans hR')
    have hf : ((A.cells.filter fun I => dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G R'.1 R'.2).filter fun I =>
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R''.1 R''.2) =
        A.cells.filter fun I => dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R''.1 R''.2 := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun I _ => ⟨fun h => h.2, fun h => ⟨h.trans hR'', h⟩⟩
    refine ⟨fun l => ?_, ?_, fun l => ?_⟩
    · change ∑ I ∈ (A.cells.filter fun I => dyadicGridCell A.G I.1 I.2 ⊆
          dyadicGridCell A.G R'.1 R'.2).filter fun I =>
            dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R''.1 R''.2, _ ≤ _
      rw [hf]; exact hs' l
    · change ∑ I ∈ (A.cells.filter fun I => dyadicGridCell A.G I.1 I.2 ⊆
          dyadicGridCell A.G R'.1 R'.2).filter fun I =>
            dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R''.1 R''.2, _ ≤ _
      rw [hf]; exact ht'
    · obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := hc' l
      exact ⟨P₁, P₂, h₁, h₂,
        c₁.mono (fun I hI => ⟨(Finset.mem_filter.mp hI.1).1, hI.2⟩) le_rfl le_rfl,
        c₂.mono (fun I hI => ⟨(Finset.mem_filter.mp hI.1).1, hI.2⟩) le_rfl le_rfl,
        e₁.mono (fun I hI => ⟨(Finset.mem_filter.mp hI.1).1, hI.2⟩),
        e₂.mono (fun I hI => ⟨(Finset.mem_filter.mp hI.1).1, hI.2⟩),
        fun I hI hIR => hP I (Finset.mem_filter.mp hI).1 hIR⟩

end ActiveSetup

open Classical in
/-- Blueprint `eq:before-absorption` on one root, after the choice of `q, α, P` (prop:normalized,
lines 2838-2888): the retained-attempt estimate. For every active setup with the level
properties there are pairwise disjoint exceptional roots of total length at most `|R|/4` such that
the active-cell minima of each pattern over the cells below no exceptional root are at most
`C η₀^{c_*} (1 + C_N) |R|`. -/
def RetainedMin (κ : LocalKernelClass) : Prop :=
  ∀ (c' Cb : ℕ) (θ₀ : ℝ), 1 ≤ c' → 0 < θ₀ → θ₀ ≤ 1 → ∃ q : ℝ, 2 < q ∧ q < 3 ∧
    ∃ cs Cfin : ℝ, 0 < cs ∧ 0 ≤ Cfin ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (N : ℕ) (d₀ : ℤ)
      (B : ActiveSetup κ c'), (∀ I ∈ B.cells, B.w I ≠ 0 → d₀ ≤ I.1 ∧ I.1 < d₀ + N) →
      B.LevelProps k Cb (Real.exp (-2 * (k : ℝ) ^ θ₀)) → ∀ p : Fin 3,
      ∃ X : Finset (ℤ × ℤ),
        (∀ c ∈ X, dyadicGridCell B.G c.1 c.2 ⊆ dyadicGridCell B.G B.R.1 B.R.2) ∧
        (∀ c ∈ X, ∀ c' ∈ X, c ≠ c' →
          Disjoint (dyadicGridCell B.G c.1 c.2) (dyadicGridCell B.G c'.1 c'.2)) ∧
        ∑ c ∈ X, dyadicGridLength B.G c.1 ≤ 1 / 4 * dyadicGridLength B.G B.R.1 ∧
        ∑ I ∈ (B.cells.filter (fun I => ¬ ∃ c ∈ X,
            dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G c.1 c.2)).filter
            (B.active (Real.exp (-(k : ℝ) ^ (Cb + 2)))),
          dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z (Fin.castSucc p) I)‖ ≤
        Cfin * Real.exp (-2 * (k : ℝ) ^ θ₀) ^ cs * (1 + finiteDepthConstant κ q N) *
          dyadicGridLength B.G B.R.1

open Classical in
/-- Blueprint prop:normalized, lines 2840-2843 and 2885-2888: restarting the retained-attempt
estimate at the exceptional roots, whose root packing has factor `4/3`, gives `eq:active-final`
on all active cells. -/
theorem activeMin_of_retainedMin {κ : LocalKernelClass} (h : RetainedMin κ) : ActiveMin κ := by
  intro c' Cb θ₀ hc' hθ₀ hθ₁
  obtain ⟨q, hq2, hq3, cs, Cfin, hcs, hCfin, K, hK⟩ := h c' Cb θ₀ hc' hθ₀ hθ₁
  refine ⟨q, hq2, hq3, cs, 4 / 3 * Cfin, hcs, by positivity, K,
    fun k hk N d₀ B hwin hprops p => ?_⟩
  set δ := Real.exp (-(k : ℝ) ^ (Cb + 2))
  set A := Cfin * Real.exp (-2 * (k : ℝ) ^ θ₀) ^ cs * (1 + finiteDepthConstant κ q N)
  have hA : 0 ≤ A := by
    have := (finiteDepthConstant_bounds κ hq2.le N).1
    have : 0 ≤ Real.exp (-2 * (k : ℝ) ^ θ₀) ^ cs := Real.rpow_nonneg (Real.exp_pos _).le _
    positivity
  set! f : ActiveSetup κ c' → ℤ × ℤ → ℝ := fun B' I => if B'.active δ I then
    dyadicGridLength B'.G I.1 * min B'.η ‖B'.Hf I (B'.z (Fin.castSucc p) I)‖ else 0
  have hrec := ActiveSetup.restart_recursion
    (fun B' => (∀ I ∈ B'.cells, B'.w I ≠ 0 → d₀ ≤ I.1 ∧ I.1 < d₀ + N) ∧
      B'.LevelProps k Cb (Real.exp (-2 * (k : ℝ) ^ θ₀)))
    (fun B' R' hB' hR' => ⟨fun I hI hw => hB'.1 I (Finset.mem_filter.mp hI).1 hw,
      ActiveSetup.LevelProps.below B' R' hB'.2 hR'⟩)
    f (fun _ _ _ => rfl) hA (fun B' hB' => by
      obtain ⟨X, h1, h2, h3, h4⟩ := hK k hk N d₀ B' hB'.1 hB'.2 p
      refine ⟨X, h1, h2, h3, ?_⟩
      rw [← Finset.sum_filter]
      exact h4) B ⟨hwin, hprops⟩
  rw [← Finset.sum_filter] at hrec
  calc _ ≤ 4 / 3 * A * dyadicGridLength B.G B.R.1 := hrec
    _ = _ := by simp only [A]; ring

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)

/-- The slots of a pattern other than its marked slot carry the basic arguments. -/
theorem z_slot_basic (p : Fin 3) (I : ℤ × ℤ) {l : Fin 4} (hl : l ≠ A.mslot p) :
    A.z (Fin.castSucc p) I l = A.B l I := by
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hl
  exact (A.pattern_data I p).2.2.2 i

open Classical in
/-- The cells of an active family containing a cell are among the active cells through its left
endpoint (the path multiplicity `M_p` of the localization). -/
theorem active_anc_card_le {δ : ℝ} (T : Finset (ℤ × ℤ)) (hT : ∀ I ∈ T, I ∈ A.cells ∧ A.active δ I)
    (I : ℤ × ℤ) :
    (T.filter fun I' => dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I'.1 I'.2).card ≤
      (A.cells.filter fun I' => dyadicGridLeft A.G I.1 I.2 ∈ dyadicGridCell A.G I'.1 I'.2 ∧
        A.active δ I').card := by
  refine Finset.card_le_card fun I' hI' => ?_
  obtain ⟨hI'T, hsub⟩ := Finset.mem_filter.mp hI'
  exact Finset.mem_filter.mpr ⟨(hT I' hI'T).1, hsub (dyadicGridCell_left_mem A.G I.1 I.2),
    (hT I' hI'T).2⟩

end ActiveSetup

open Classical in
/-- Blueprint prop:base (line 1655) and line 2839 (the active path multiplicity for the attempt):
at the activity threshold `δ_k = e^{-k^{C_b+2}}`, every point lies in at most
`exp(C k^{3 C_b + 2})` active cells of a setup with the level properties. -/
theorem active_mult_bound (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) (Cb : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ (B : ActiveSetup κ c₀) (η₀ : ℝ),
      B.LevelProps k Cb η₀ → ∀ y : ℝ,
        ((B.cells.filter fun I => y ∈ dyadicGridCell B.G I.1 I.2 ∧
          B.active (Real.exp (-(k : ℝ) ^ (Cb + 2))) I).card : ℝ) ≤
          Real.exp (C * (k : ℝ) ^ (3 * Cb + 2)) := by
  obtain ⟨C, hC1, hcount⟩ := ActiveSetup.active_count κ c₀ hc
  set c1 : ℝ := 172802 + Real.log (sliceConst κ)
  have hsl : 1 ≤ sliceConst κ := by
    unfold sliceConst
    have := localKernelSupBound_nonneg κ
    have := kernelLipConst_nonneg κ
    linarith
  have hlogsl : 0 ≤ Real.log (sliceConst κ) := Real.log_nonneg hsl
  refine ⟨5 + (C : ℝ) + (C : ℝ) * c1, by positivity, fun k hk B η₀ hB y => ?_⟩
  obtain ⟨-, hH1, hHk, -, hLk, -⟩ := hB
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set m := 3 * Cb + 2
  have hkCb : (1 : ℝ) ≤ (k : ℝ) ^ Cb := one_le_pow₀ hk1
  have hkm : (1 : ℝ) ≤ (k : ℝ) ^ m := one_le_pow₀ hk1
  have hCbm : (k : ℝ) ^ Cb ≤ (k : ℝ) ^ m := pow_le_pow_right₀ hk1 (by omega)
  have h3m : (k : ℝ) ^ (3 * Cb) ≤ (k : ℝ) ^ m := pow_le_pow_right₀ hk1 (by omega)
  have h2m : (k : ℝ) ^ (Cb + 2) ≤ (k : ℝ) ^ m := pow_le_pow_right₀ hk1 (by omega)
  set δ := Real.exp (-(k : ℝ) ^ (Cb + 2))
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    have := pow_nonneg (Nat.cast_nonneg (α := ℝ) k) (Cb + 2)
    exact Real.exp_le_one_iff.mpr (by linarith only [this])
  have h := hcount B δ hδ0 hδ1 y
  -- the logarithmic terms
  have hlogH0 : 0 ≤ Real.log B.H := Real.log_nonneg hH1
  have hlogH : Real.log B.H ≤ (k : ℝ) ^ Cb := by
    have := Real.log_le_log (by linarith only [hH1]) hHk
    rwa [Real.log_exp] at this
  have hbud : Real.log (chartTranslationBudget B.H) ≤ 800 * (k : ℝ) ^ (3 * Cb) := by
    unfold chartTranslationBudget logarithmicSize
    rw [Real.log_exp]
    have h1 : 1 + Real.log B.H ≤ 2 * (k : ℝ) ^ Cb := by linarith only [hkCb, hlogH]
    have h2 : (1 + Real.log B.H) ^ 3 ≤ (2 * (k : ℝ) ^ Cb) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hlogH0]) h1 3
    rw [mul_pow, ← pow_mul] at h2
    rw [mul_comm Cb 3] at h2
    nlinarith only [h2]
  have hbud0 : 0 ≤ Real.log (chartTranslationBudget B.H) := by
    unfold chartTranslationBudget logarithmicSize
    rw [Real.log_exp]; positivity
  have hlogδ : Real.log δ⁻¹ = (k : ℝ) ^ (Cb + 2) := by
    rw [Real.log_inv, Real.log_exp]; ring
  set X := 216 * Real.log (chartTranslationBudget B.H) + Real.log (sliceConst κ) +
    2 * Real.log δ⁻¹
  have hX0 : 0 ≤ X := by
    simp only [X, hlogδ]; positivity
  have hX : X ≤ c1 * (k : ℝ) ^ m := by
    simp only [X, hlogδ, c1]
    nlinarith only [hlogsl, hkm, h3m, h2m, hbud]
  -- the label factor
  have hL3 : (Fintype.card B.L : ℝ) ^ 3 ≤ Real.exp (3 * (k : ℝ) ^ Cb) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hLk 3
    rwa [← Real.exp_nat_mul] at this
  have hpow : (C : ℝ) * X ^ C ≤ Real.exp ((C : ℝ) + (C : ℝ) * c1 * (k : ℝ) ^ m) := by
    rw [Real.exp_add]
    refine mul_le_mul (by linarith only [Real.add_one_le_exp (C : ℝ)])
      ((pow_le_exp_mul hX0 C).trans (Real.exp_le_exp.mpr ?_)) (by positivity) (by positivity)
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    calc (C : ℝ) * X ≤ (C : ℝ) * (c1 * (k : ℝ) ^ m) := by gcongr
      _ = _ := by ring
  refine h.trans ?_
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2
    nlinarith only [Real.add_one_le_exp (1 : ℝ), Real.exp_pos 1,
      show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
  calc 4 * (Fintype.card B.L : ℝ) ^ 3 * ((C : ℝ) * X ^ C)
      ≤ Real.exp 2 * Real.exp (3 * (k : ℝ) ^ Cb) *
          Real.exp ((C : ℝ) + (C : ℝ) * c1 * (k : ℝ) ^ m) := by
        gcongr
    _ = Real.exp (2 + 3 * (k : ℝ) ^ Cb + ((C : ℝ) + (C : ℝ) * c1 * (k : ℝ) ^ m)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp ((5 + (C : ℝ) + (C : ℝ) * c1) * (k : ℝ) ^ m) := by
        refine Real.exp_le_exp.mpr ?_
        have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
        nlinarith only [hkCb, hCbm]

/-! ### The eventual growth bounds of the parameters (blueprint lines 2869-2888) -/

section
open Filter Real Asymptotics

/-- Quasi-polynomial factors are eventually below every stretched exponential: for `C ≥ 0` and
`β, θ > 0`, eventually `x^a e^{C (1 + log 2x)²} ≤ e^{β x^θ}`. -/
theorem eventually_qpoly_le_exp (a : ℝ) {C β θ : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (hθ : 0 < θ) :
    ∀ᶠ x : ℝ in atTop, x ^ a * Real.exp (C * (1 + Real.log (2 * x)) ^ 2) ≤
      Real.exp (β * x ^ θ) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ θ := isLittleO_log_rpow_atTop hθ
  have h2 : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop] fun x => x ^ θ :=
    isLittleO_log_rpow_rpow_atTop 2 hθ
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ θ :=
    isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hθ)))
  set c := 1 + Real.log 2 with hcdef
  have hsum : (fun x : ℝ => a * Real.log x + C * (2 * c ^ 2 * 1 + 2 * Real.log x ^ (2 : ℝ)))
      =o[atTop] fun x => x ^ θ :=
    (h1.const_mul_left a).add (((hc.const_mul_left (2 * c ^ 2)).add
      (h2.const_mul_left 2)).const_mul_left C)
  filter_upwards [hsum.def hβ, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg hx0.le _
  rw [Real.norm_of_nonneg hxθ, Real.norm_eq_abs] at hx
  have hl2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  have hsq : (1 + Real.log (2 * x)) ^ 2 ≤ 2 * c ^ 2 * 1 + 2 * Real.log x ^ (2 : ℝ) := by
    rw [hl2, Real.rpow_two, hcdef]
    nlinarith only [sq_nonneg (1 + Real.log 2 - Real.log x)]
  rw [← Real.exp_log (Real.rpow_pos_of_pos hx0 a), ← Real.exp_add, Real.exp_le_exp,
    Real.log_rpow hx0]
  have habs := le_abs_self (a * Real.log x + C * (2 * c ^ 2 * 1 + 2 * Real.log x ^ (2 : ℝ)))
  have := mul_le_mul_of_nonneg_left hsq hC
  linarith only [hx, habs, this]

/-- The natural-number form of `eventually_qpoly_le_exp`. -/
theorem eventually_nat_qpoly_le_exp (a : ℝ) {C β θ : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (hθ : 0 < θ) :
    ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ a * Real.exp (C * (1 + Real.log (2 * (k : ℝ))) ^ 2) ≤
      Real.exp (β * (k : ℝ) ^ θ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_qpoly_le_exp a hC hβ hθ)

/-- `eventually_nat_qpoly_le_exp` with a constant factor `A ≥ 0`. -/
theorem eventually_nat_const_qpoly_le_exp (A a : ℝ) {C β θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hβ : 0 < β) (hθ : 0 < θ) :
    ∀ᶠ k : ℕ in atTop, A * (k : ℝ) ^ a * Real.exp (C * (1 + Real.log (2 * (k : ℝ))) ^ 2) ≤
      Real.exp (β * (k : ℝ) ^ θ) := by
  filter_upwards [eventually_nat_qpoly_le_exp (a + 1) hC hβ hθ,
    eventually_ge_atTop ⌈A + 1⌉₊] with k hk hkA
  have hkA' : A + 1 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hkA)
  have hk0 : (0 : ℝ) < k := by linarith only [hkA', hA]
  have hpow : A * (k : ℝ) ^ a ≤ (k : ℝ) ^ (a + 1) := by
    rw [Real.rpow_add hk0, Real.rpow_one, mul_comm ((k : ℝ) ^ a)]
    exact mul_le_mul_of_nonneg_right (by linarith only [hkA']) (Real.rpow_nonneg hk0.le _)
  exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans hk

/-- Polynomial and lower exponential factors are eventually below a higher exponential: for
natural `s < t`, `β > 0` and real `A, a, B`, eventually `A k^a e^{B k^s} ≤ e^{β k^t}`. -/
theorem eventually_nat_poly_exp_le_exp (A a B : ℝ) {s t : ℕ} (hst : s < t) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ k : ℕ in atTop, A * (k : ℝ) ^ a * Real.exp (B * (k : ℝ) ^ s) ≤
      Real.exp (β * (k : ℝ) ^ t) := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) hst
  have hpow : (fun x : ℝ => x ^ s) =o[atTop] fun x => x ^ t := isLittleO_pow_pow_atTop_of_lt hst
  have hrt : (fun x : ℝ => x ^ (t : ℝ)) = fun x => x ^ t := by
    funext x; exact Real.rpow_natCast x t
  have hlog : (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ t := by
    have := isLittleO_log_rpow_atTop (show (0 : ℝ) < t by exact_mod_cast ht)
    rwa [hrt] at this
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ t :=
    isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp (tendsto_pow_atTop ht.ne')))
  have hsum : (fun x : ℝ => Real.log (|A| + 1) * 1 + a * Real.log x + B * x ^ s) =o[atTop]
      fun x => x ^ t :=
    ((hc.const_mul_left (Real.log (|A| + 1))).add (hlog.const_mul_left a)).add
      (hpow.const_mul_left B)
  have hev : ∀ᶠ x : ℝ in atTop, A * x ^ a * Real.exp (B * x ^ s) ≤ Real.exp (β * x ^ t) := by
    filter_upwards [hsum.def hβ, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith only [hx1]
    have hxt : 0 ≤ x ^ t := pow_nonneg hx0.le _
    rw [Real.norm_of_nonneg hxt, Real.norm_eq_abs] at hx
    have habs := le_abs_self (Real.log (|A| + 1) * 1 + a * Real.log x + B * x ^ s)
    have hAle : A ≤ Real.exp (Real.log (|A| + 1)) := by
      rw [Real.exp_log (by positivity)]; linarith only [le_abs_self A]
    have hxa : x ^ a = Real.exp (a * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, mul_comm]
    calc A * x ^ a * Real.exp (B * x ^ s)
        ≤ Real.exp (Real.log (|A| + 1)) * x ^ a * Real.exp (B * x ^ s) := by
          gcongr
      _ = Real.exp (Real.log (|A| + 1) * 1 + a * Real.log x + B * x ^ s) := by
          rw [hxa, ← Real.exp_add, ← Real.exp_add, mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact tendsto_natCast_atTop_atTop.eventually hev

/-- Polynomial domination: for natural `a < t`, eventually `A k^a ≤ k^t`. -/
theorem eventually_nat_pow_dom (A : ℝ) {a t : ℕ} (hat : a < t) :
    ∀ᶠ k : ℕ in atTop, A * (k : ℝ) ^ a ≤ (k : ℝ) ^ t := by
  filter_upwards [eventually_ge_atTop ⌈|A| + 1⌉₊] with k hk
  have hkA : |A| + 1 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hk1 : (1 : ℝ) ≤ k := by linarith only [abs_nonneg A, hkA]
  have h1 : (k : ℝ) ≤ (k : ℝ) ^ (t - a) := le_self_pow₀ hk1 (by omega)
  have h2 : (k : ℝ) ^ t = (k : ℝ) ^ (t - a) * (k : ℝ) ^ a := by
    rw [← pow_add]; congr 1; omega
  have h0 : (0 : ℝ) ≤ (k : ℝ) ^ a := pow_nonneg (by linarith only) _
  rw [h2]
  have : A ≤ (k : ℝ) ^ (t - a) := by linarith only [le_abs_self A, hkA, h1]
  exact mul_le_mul_of_nonneg_right this h0

/-- Eventually `L + 2 k^b ≤ 3 k^b` for `b ≥ 1`. -/
theorem eventually_nat_add_pow_le (L : ℝ) {b : ℕ} (hb : 1 ≤ b) :
    ∀ᶠ k : ℕ in atTop, L + 2 * (k : ℝ) ^ b ≤ 3 * (k : ℝ) ^ b := by
  filter_upwards [eventually_nat_pow_dom L (show 0 < b by omega)] with k hk
  rw [pow_zero, mul_one] at hk
  linarith only [hk]

/-- Eventually `M ≤ log k`. -/
theorem eventually_nat_le_log (M : ℝ) : ∀ᶠ k : ℕ in atTop, M ≤ Real.log k := by
  filter_upwards [eventually_ge_atTop ⌈Real.exp M⌉₊] with k hk
  have h1 : Real.exp M ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have h0 : 0 < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos M) h1
  calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
    _ ≤ Real.log k := Real.log_le_log (Real.exp_pos M) h1

/-- The polynomial standing bounds of the retained-attempt estimate at accuracy `k`, for the
exponent `Y = L₄ + 2 k^b` of the height and column budget (blueprint lines 2853-2869: all degrees
are absolute): the colour count, vertex bound, fuel, source height and counts are below `k^c`
(attempt) and `k^{cc}` (leaf), and the curvature thresholds below `k^{cc}`. -/
theorem retained_numeric_poly {L₄ lW cH Ca : ℝ} {b m c₃ c C a₀ cc Dg : ℕ} (hL₄ : 0 ≤ L₄)
    (hlW : 0 ≤ lW) (hcH : 0 ≤ cH) (hCa : 0 < Ca) (hb : 1 ≤ b) (hbc : 30 * b < c) (hmc : m < c)
    (hc₃ : c₃ < a₀) (hfuel : 90 * b + 100 ≤ c) (hca : c < a₀) (hCa₀ : C < a₀)
    (hcc1 : a₀ * Dg < cc) (hcc2 : a₀ < cc) :
    ∀ᶠ k : ℕ in atTop,
      6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1 + 6 ≤ (k : ℝ) ^ c ∧
      (L₄ + 2 * (k : ℝ) ^ b) + 3 ≤ (k : ℝ) ^ c ∧
      2 * (Real.log (4 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1)) / Real.log 2) + 2 ≤
        c * (Real.log k + 1) ∧
      cH + 2 * (lW + (L₄ + 2 * (k : ℝ) ^ b)) ≤ (k : ℝ) ^ c ∧
      Real.exp (Ca * (k : ℝ) ^ m) + 1 ≤ Real.exp ((k : ℝ) ^ c) ∧
      2 * Real.exp (L₄ + 2 * (k : ℝ) ^ b) ≤ Real.exp ((k : ℝ) ^ c) ∧
      Real.log 18 + 2 * (lW + (L₄ + 2 * (k : ℝ) ^ b)) ≤ (k : ℝ) ^ cc ∧
      Dg * (1 + (cH + 2 * (lW + (L₄ + 2 * (k : ℝ) ^ b))) + Real.log 6 +
        3 * ((L₄ + 2 * (k : ℝ) ^ b) + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2) + (k : ℝ) ^ c₃ +
        2 * ((L₄ + 2 * (k : ℝ) ^ b) + 3)) ^ Dg ≤ (k : ℝ) ^ cc ∧
      (k : ℝ) ^ C + 2 * (L₄ + 2 * (k : ℝ) ^ b) ≤ (k : ℝ) ^ (cc + 1) ∧
      Real.log 20 + ((L₄ + 2 * (k : ℝ) ^ b) + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2) ≤
        (k : ℝ) ^ cc ∧
      Real.log 2 + (L₄ + 2 * (k : ℝ) ^ b) ≤ (k : ℝ) ^ cc ∧
      20 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1) + 61 ≤ (k : ℝ) ^ cc ∧
      lW + (L₄ + 2 * (k : ℝ) ^ b) + 1 ≤ (k : ℝ) ^ cc ∧
      cH + 2 * (lW + (L₄ + 2 * (k : ℝ) ^ b)) ≤ (k : ℝ) ^ cc ∧
      96 * (4 * (6000 ^ 30 * (L₄ + 2 * (k : ℝ) ^ b) ^ 30 + 1)) ≤ (k : ℝ) ^ cc := by
  set! AL : ℝ := 6000 ^ 30 * 3 ^ 30 + 1 with hAL
  have hAL1 : 1 ≤ AL := by rw [hAL]; norm_num
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  -- the exponents
  have hba : b ≤ a₀ := by omega
  have hma : m ≤ a₀ := by omega
  have h30cc : 30 * b < cc := by omega
  have hbcc : b < cc := by omega
  filter_upwards [eventually_nat_add_pow_le L₄ hb, eventually_ge_atTop 1,
    eventually_nat_pow_dom (AL + 6) hbc, eventually_nat_pow_dom 6 (show b < c by omega),
    eventually_nat_le_log ((3 * Real.log (4 * AL) + 2) / 100),
    eventually_nat_pow_dom (cH + 2 * lW + 6) (show b < c by omega),
    eventually_nat_poly_exp_le_exp 2 0 Ca hmc one_pos,
    eventually_nat_poly_exp_le_exp 2 0 3 (show b < c by omega) one_pos,
    eventually_nat_pow_dom (Real.log 18 + 2 * lW + 6) hbcc,
    eventually_nat_pow_dom (Dg * (13 + cH + 2 * lW + Real.log 6 + 21 + 3 + 3 * Ca + 1) ^ Dg) hcc1,
    eventually_nat_pow_dom 7 (show a₀ < cc + 1 by omega),
    eventually_nat_pow_dom (Real.log 20 + 3 + 1 + Ca + 2) hcc2,
    eventually_nat_pow_dom (Real.log 2 + 3) hbcc,
    eventually_nat_pow_dom (20 * AL + 61) h30cc,
    eventually_nat_pow_dom (lW + 4) hbcc,
    eventually_nat_pow_dom (cH + 2 * lW + 6) hbcc,
    eventually_nat_pow_dom (384 * AL) h30cc]
    with k hY hk1 d1 d2 dlog d5 d6 d7 d8 d9 d11 d12 d13 d14 d15 d16 d17
  have hu1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set u : ℝ := (k : ℝ) with hudef
  set! Y : ℝ := L₄ + 2 * u ^ b with hYdef
  rewrite [← hYdef] at hY ⊢
  have hub1 : 1 ≤ u ^ b := one_le_pow₀ hu1
  have hY0 : 0 ≤ Y := by positivity
  have hpow : ∀ x y : ℕ, x ≤ y → u ^ x ≤ u ^ y := fun x y h => pow_le_pow_right₀ hu1 h
  -- the colour count `P₃₀ = 6000^{30} Y^{30} + 1 ≤ A_L k^{30 b}`
  have hY30 : Y ^ 30 ≤ 3 ^ 30 * u ^ (30 * b) := by
    calc Y ^ 30 ≤ (3 * u ^ b) ^ 30 := pow_le_pow_left₀ hY0 hY 30
      _ = 3 ^ 30 * u ^ (30 * b) := by rw [mul_pow, ← pow_mul, mul_comm b]
  have hu30 : 1 ≤ u ^ (30 * b) := one_le_pow₀ hu1
  have hP30 : 6000 ^ 30 * Y ^ 30 + 1 ≤ AL * u ^ (30 * b) := by
    rw [hAL]; nlinarith only [hY30, hu30]
  have hP300 : 0 ≤ 6000 ^ 30 * Y ^ 30 + 1 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hP30, d1, hu30]
  · nlinarith only [hY, d2, hub1]
  · -- the fuel: `2 log₂ F + 2 ≤ c (log k + 1)`
    have hlu : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hF : Real.log (4 * (6000 ^ 30 * Y ^ 30 + 1)) ≤
        Real.log (4 * AL) + 30 * b * Real.log u := by
      have h1 : 4 * (6000 ^ 30 * Y ^ 30 + 1) ≤ 4 * AL * u ^ (30 * b) := by linarith only [hP30]
      have h2 := Real.log_le_log (by positivity) h1
      have h3 : Real.log (4 * AL * u ^ (30 * b)) = Real.log (4 * AL) + 30 * b * Real.log u := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      linarith only [h2, h3]
    have hFl0 : 0 ≤ Real.log (4 * (6000 ^ 30 * Y ^ 30 + 1)) := by
      have : 0 ≤ 6000 ^ 30 * Y ^ 30 := by positivity
      exact Real.log_nonneg (by linarith only [this])
    have h3 : 2 * (Real.log (4 * (6000 ^ 30 * Y ^ 30 + 1)) / Real.log 2) ≤
        3 * Real.log (4 * (6000 ^ 30 * Y ^ 30 + 1)) := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith only [hl2])]
      nlinarith only [hl2, hFl0]
    have hc : (90 * b + 100 : ℝ) ≤ c := by exact_mod_cast hfuel
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    have e2 := mul_le_mul_of_nonneg_right hc hlu
    have e4 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have dlog' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 100)).mp dlog
    have e5 : (90 * b + 100) * Real.log u = 90 * b * Real.log u + 100 * Real.log u := by ring
    rw [e5] at e2
    have e6 : (c : ℝ) * (Real.log u + 1) = c * Real.log u + c := by ring
    rw [e6]
    set! lF := Real.log (4 * (6000 ^ 30 * Y ^ 30 + 1)) with hlF
    rewrite [← hlF] at hF hFl0 h3 ⊢
    set! lA := Real.log (4 * AL) with hlA
    rewrite [← hlA] at dlog dlog' hF
    set L := Real.log u with hL
    calc 2 * (lF / Real.log 2) + 2 ≤ 3 * lF + 2 := by linarith only [h3]
      _ ≤ 3 * (lA + 30 * b * L) + 2 := by linarith only [hF]
      _ = 90 * b * L + (3 * lA + 2) := by ring
      _ ≤ 90 * b * L + L * 100 := by linarith only [dlog']
      _ = 90 * b * L + 100 * L := by ring
      _ ≤ c * L := e2
      _ ≤ c * L + c := by linarith only [e4]
  · nlinarith only [hY, d5, hub1, hcH, hlW]
  · have h := d6
    simp only [Real.rpow_zero, mul_one, one_mul] at h
    have h0 : 1 ≤ Real.exp (Ca * u ^ m) := Real.one_le_exp (by positivity)
    linarith only [h, h0]
  · have h := d7
    simp only [Real.rpow_zero, mul_one, one_mul] at h
    have : Real.exp Y ≤ Real.exp (3 * u ^ b) := Real.exp_le_exp.mpr hY
    linarith only [h, this]
  · have hl18 : 0 ≤ Real.log 18 := Real.log_nonneg (by norm_num)
    nlinarith only [hY, d8, hub1, hlW, hl18]
  · -- the curvature thresholds
    set base := 1 + (cH + 2 * (lW + Y)) + Real.log 6 + 3 * (Y + u ^ C + Ca * u ^ m + 2) +
      u ^ c₃ + 2 * (Y + 3) with hbase
    have hua : 1 ≤ u ^ a₀ := one_le_pow₀ hu1
    have h1 : u ^ b ≤ u ^ a₀ := hpow _ _ hba
    have h2 : u ^ C ≤ u ^ a₀ := hpow _ _ hCa₀.le
    have h3 : u ^ m ≤ u ^ a₀ := hpow _ _ hma
    have h4 : u ^ c₃ ≤ u ^ a₀ := hpow _ _ hc₃.le
    have hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hb0 : 0 ≤ base := by positivity
    have hbB : base ≤ (13 + cH + 2 * lW + Real.log 6 + 21 + 3 + 3 * Ca + 1) * u ^ a₀ := by
      rw [hbase]; nlinarith only [hY, h1, h2, h3, h4, hua, hCa, hcH, hlW, hl6, hL₄]
    have hp := pow_le_pow_left₀ hb0 hbB Dg
    rw [mul_pow, ← pow_mul] at hp
    have hD : (0 : ℝ) ≤ Dg := Nat.cast_nonneg _
    calc (Dg : ℝ) * base ^ Dg ≤ Dg * ((13 + cH + 2 * lW + Real.log 6 + 21 + 3 + 3 * Ca + 1) ^ Dg *
          u ^ (a₀ * Dg)) := mul_le_mul_of_nonneg_left hp hD
      _ = Dg * (13 + cH + 2 * lW + Real.log 6 + 21 + 3 + 3 * Ca + 1) ^ Dg * u ^ (a₀ * Dg) := by
          ring
      _ ≤ _ := d9
  · have h1 : u ^ b ≤ u ^ a₀ := hpow _ _ hba
    have h2 : u ^ C ≤ u ^ a₀ := hpow _ _ hCa₀.le
    nlinarith only [hY, h1, h2, d11]
  · have hua : 1 ≤ u ^ a₀ := one_le_pow₀ hu1
    have h1 : u ^ b ≤ u ^ a₀ := hpow _ _ hba
    have h2 : u ^ C ≤ u ^ a₀ := hpow _ _ hCa₀.le
    have h3 : u ^ m ≤ u ^ a₀ := hpow _ _ hma
    have hl20 : 0 ≤ Real.log 20 := Real.log_nonneg (by norm_num)
    nlinarith only [hY, h1, h2, h3, hua, d12, hCa, hl20, hL₄]
  · have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith only [hY, d13, hub1, hl2']
  · nlinarith only [hP30, d14, hu30]
  · nlinarith only [hY, d15, hub1, hlW]
  · nlinarith only [hY, d16, hub1, hcH, hlW]
  · nlinarith only [hP30, d17, hu30]

/-- If `4 X e^u ≤ e^t` then `X e^{-t} ≤ e^{-u}/4`. -/
theorem mul_exp_neg_le {X t u : ℝ} (h : 4 * X * Real.exp u ≤ Real.exp t) :
    X * Real.exp (-t) ≤ Real.exp (-u) / 4 := by
  rw [Real.exp_neg, Real.exp_neg]
  have h2 : X * (Real.exp t)⁻¹ * (4 * Real.exp u) ≤ 1 := by
    calc X * (Real.exp t)⁻¹ * (4 * Real.exp u) = (4 * X * Real.exp u) * (Real.exp t)⁻¹ := by ring
      _ ≤ Real.exp t * (Real.exp t)⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)
      _ = 1 := mul_inv_cancel₀ (Real.exp_pos t).ne'
  have h3 : 0 < 4 * Real.exp u := by positivity
  calc X * (Real.exp t)⁻¹ = X * (Real.exp t)⁻¹ * (4 * Real.exp u) / (4 * Real.exp u) := by
        field_simp
    _ ≤ 1 / (4 * Real.exp u) := div_le_div_of_nonneg_right h2 h3.le
    _ = (Real.exp u)⁻¹ / 4 := by field_simp



end
end TrilinearHT.Auto
end
