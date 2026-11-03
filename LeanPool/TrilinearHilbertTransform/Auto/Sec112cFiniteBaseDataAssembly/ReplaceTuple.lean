/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec112cFiniteBaseDataAssembly.Setup

/-!
# Trilinear Hilbert transform: replaceTuple
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
section ReplaceTuple
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ c₁ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {a i k b : Fin 4} (Bp D : ℝ)
  (pkga : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b Bp D c₁)
  (pkgb : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) b i k a Bp D c₁)
  {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)

open scoped Classical in
private def ReplaceTupleHcellStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (c₀ : ℕ)
    (c₁ : ℕ)
    (H : ℝ)
    (Xi : LowList G J N J c₀ H)
    (Xk : LowList G J N J c₀ H)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (Bp : ℝ)
    (D : ℝ)
    (pkga : (K K' : ℤ × ℤ) → (li : Xi.Λ) → (lk : Xk.Λ) → PredictorPackage κ (Xi.chart K li)
      (Xk.chart K' lk) a i k b Bp D c₁)
    (pkgb : (K K' : ℤ × ℤ) → (li : Xi.Λ) → (lk : Xk.Λ) → PredictorPackage κ (Xi.chart K li)
      (Xk.chart K' lk) b i k a Bp D c₁)
    (ε : ℝ)
    (hε0 : (0 : ℝ) < ε)
    (hε1 : ε ≤ (1 : ℝ))
    (_ : a ≠ i)
    (_ : a ≠ k)
    (_ : a ≠ b)
    (_ : i ≠ k)
    (_ : i ≠ b)
    (_ : k ≠ b)
    (K₀ : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (q : ℝ)
    (ka : ℕ)
    (kb : ℕ)
    (c₂ : ℕ)
    (Ba : ℝ)
    (Bb : ℝ)
    (_ : (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).Hyp)
    (_ : (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).Hyp)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (Ka : ℤ × ℤ)
    (Kb : ℤ × ℤ)
    (R : ℤ × ℤ)
    (hR : R ∈ dyadicFiniteTree G J N)
    (ga : ℤ × ℤ → ℝ → ℂ)
    (gb : ℤ × ℤ → ℝ → ℂ)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (Cga : ℝ)
    (Cgb : ℝ)
    (_ : ∀ (I : ℤ × ℤ), Measurable (ga I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (gb I))
    (_ : (∀ (I : ℤ × ℤ), Measurable (zga I) ∧ MemLp (zga I) (2 : ℝ≥0∞) (volume.restrict
      (dyadicGridCell G I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G
      J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G J' (f a) zga Cga ∧
      HasDepthEnergy G J' (f a) zga (1 : ℝ))
    (_ : (∀ (I : ℤ × ℤ), Measurable (zgb I) ∧ MemLp (zgb I) (2 : ℝ≥0∞) (volume.restrict
      (dyadicGridCell G I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G
      J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G J' (f b) zgb Cgb ∧
      HasDepthEnergy G J' (f b) zgb (1 : ℝ))
    (T : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀
      Ma (f a) w q ka c₂ Ba).Nc ∧ (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma
      (f a) w q ka c₂ Ba).tree.seg I = Ka ∧ (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0
      hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.seg I = Kb ∧ dyadicGridCell G I.1 I.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zga I y =
      ga I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = gb I y),
  let Sa : AccSetup :=
    predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba
  let Sb : AccSetup :=
    predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb
  ∀ (_ : (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.Hyp),
  let Fb : ℝ → ℂ :=
    (dyadicGridCell G J.1 J.2).indicator (f b)
  ∀ (_ : Fb = (dyadicGridCell G J.1 J.2).indicator (f b))
    (_ : Measurable (f a))
    (_ : Measurable (f b)),
  let zbA : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) (y : ℝ) => Fb y + -zgb I y
  ∀ (_ : zbA = fun (I : ℤ × ℤ) (y : ℝ) => Fb y + -zgb I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable (zbA I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zbA I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2))),
  let zPa : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) then ((Sa.system Ka).family R
      hR).delayed Sa.input K₀ I else (0 : ℝ → ℂ)
  ∀ (_ : zPa = fun (I : ℤ × ℤ) => if I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) then ((Sa.system
      Ka).family R hR).delayed Sa.input K₀ I else (0 : ℝ → ℂ)),
  let zbB : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) (y : ℝ) => zPa I y + -zga I y
  ∀ (_ : zbB = fun (I : ℤ × ℤ) (y : ℝ) => zPa I y + -zga I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable (zbB I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zbB I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2))),
  ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (f a -
    ga I) (Xi.val I) (Xk.val I) (f b - gb I)) - localProgressionForm (dyadicGridLength
    G I.1) (w I) (slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 - ga I)
    (Xi.val I) (Xk.val I) (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 - gb I))‖ ≤
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (f a) (Xi.val
    I) (Xk.val I) (zbA I)) - localProgressionForm (dyadicGridLength G I.1) (w I)
    (slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2) (Xi.val I) (Xk.val I)
    (zbA I))‖ + ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 b i k (f
    b) (Xi.val I) (Xk.val I) (zbB I)) - localProgressionForm (dyadicGridLength G I.1)
    (w I) (slots4 b i k (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2) (Xi.val I)
    (Xk.val I) (zbB I))‖


open scoped Classical in
private def ReplaceTupleStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (c₀ : ℕ)
    (c₁ : ℕ)
    (H : ℝ)
    (Xi : LowList G J N J c₀ H)
    (Xk : LowList G J N J c₀ H)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (Bp : ℝ)
    (D : ℝ)
    (pkga : (K K' : ℤ × ℤ) → (li : Xi.Λ) → (lk : Xk.Λ) → PredictorPackage κ (Xi.chart K li)
      (Xk.chart K' lk) a i k b Bp D c₁)
    (pkgb : (K K' : ℤ × ℤ) → (li : Xi.Λ) → (lk : Xk.Λ) → PredictorPackage κ (Xi.chart K li)
      (Xk.chart K' lk) b i k a Bp D c₁)
    (ε : ℝ)
    (hε0 : (0 : ℝ) < ε)
    (hε1 : ε ≤ (1 : ℝ))
    (_ : a ≠ i)
    (_ : a ≠ k)
    (_ : a ≠ b)
    (_ : i ≠ k)
    (_ : i ≠ b)
    (_ : k ≠ b)
    (_ : (1 : ℝ) ≤ D)
    (K₀ : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (q : ℝ)
    (ka : ℕ)
    (kb : ℕ)
    (c₂ : ℕ)
    (Ba : ℝ)
    (Bb : ℝ)
    (_ : (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).Hyp)
    (_ : (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).Hyp)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (Ka : ℤ × ℤ)
    (Kb : ℤ × ℤ)
    (_ : Ka ∈ (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      Ba).tree.roots)
    (_ : Kb ∈ (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      Bb).tree.roots)
    (R : ℤ × ℤ)
    (hR : R ∈ dyadicFiniteTree G J N)
    (ga : ℤ × ℤ → ℝ → ℂ)
    (gb : ℤ × ℤ → ℝ → ℂ)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (Cga : ℝ)
    (Cgb : ℝ)
    (_ : (0 : ℝ) ≤ Cga)
    (_ : (0 : ℝ) ≤ Cgb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (ga I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (gb I))
    (_ : (∀ (I : ℤ × ℤ), Measurable (zga I) ∧ MemLp (zga I) (2 : ℝ≥0∞) (volume.restrict
      (dyadicGridCell G I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G
      J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G J' (f a) zga Cga ∧
      HasDepthEnergy G J' (f a) zga (1 : ℝ))
    (_ : (∀ (I : ℤ × ℤ), Measurable (zgb I) ∧ MemLp (zgb I) (2 : ℝ≥0∞) (volume.restrict
      (dyadicGridCell G I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G
      J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G J' (f b) zgb Cgb ∧
      HasDepthEnergy G J' (f b) zgb (1 : ℝ))
    (T : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀
      Ma (f a) w q ka c₂ Ba).Nc ∧ (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma
      (f a) w q ka c₂ Ba).tree.seg I = Ka ∧ (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0
      hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.seg I = Kb ∧ dyadicGridCell G I.1 I.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zga I y =
      ga I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = gb I y),
  let Sa : AccSetup :=
    predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba
  let Sb : AccSetup :=
    predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb
  let Ea : ℝ :=
    (2 : ℝ) * Real.exp (-Bp) * ((2 : ℝ) * (compressionOneConst ((Sa.system Ka).rooted R)
      + (↑K₀ : ℝ)) + (1 : ℝ)) + D ^ (2 : ℕ) * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + ((1 : ℝ)
      + (↑K₀ : ℝ)) * √ε) * ((1 : ℝ) + D) ^ (4 : ℕ))
  let Eb : ℝ :=
    (2 : ℝ) * Real.exp (-Bp) * ((2 : ℝ) * (compressionOneConst ((Sb.system Kb).rooted R)
      + (↑K₀ : ℝ)) + (1 : ℝ)) + D ^ (2 : ℕ) * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + ((1 : ℝ)
      + (↑K₀ : ℝ)) * √ε) * ((1 : ℝ) + D) ^ (4 : ℕ))
  ∀ (_ : (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.Hyp),
  let Fa : ℝ → ℂ :=
    (dyadicGridCell G J.1 J.2).indicator (f a)
  let Fb : ℝ → ℂ :=
    (dyadicGridCell G J.1 J.2).indicator (f b)
  ∀ (_ : Fb = (dyadicGridCell G J.1 J.2).indicator (f b))
    (_ : Measurable (f a))
    (_ : Measurable (f b))
    (_ : MemLp Fb (2 : ℝ≥0∞) volume),
  let zbA : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) (y : ℝ) => Fb y + -zgb I y
  ∀ (_ : zbA = fun (I : ℤ × ℤ) (y : ℝ) => Fb y + -zgb I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable (zbA I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zbA I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2)))
    (_ : ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2
      → IsAdmissibleOpponent G J' Fb zbA ((2 : ℝ) * ((1 : ℝ) + Cgb) + (4 : ℝ)) ∧
      HasDepthEnergy G J' Fb zbA ((2 : ℝ) * ((1 : ℝ) + Cgb) + (4 : ℝ))),
  let zPa : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) then ((Sa.system Ka).family R
      hR).delayed Sa.input K₀ I else (0 : ℝ → ℂ)
  ∀ (_ : zPa = fun (I : ℤ × ℤ) => if I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) then ((Sa.system
      Ka).family R hR).delayed Sa.input K₀ I else (0 : ℝ → ℂ)),
  let cc : ℝ :=
    compressionOneConst ((Sa.system Ka).rooted R)
  ∀ (_ : cc = compressionOneConst ((Sa.system Ka).rooted R))
    (_ : (0 : ℝ) ≤ cc),
  let zbB : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) (y : ℝ) => zPa I y + -zga I y
  ∀ (_ : zbB = fun (I : ℤ × ℤ) (y : ℝ) => zPa I y + -zga I y)
    (_ : ∀ (I : ℤ × ℤ), Measurable (zbB I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zbB I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2)))
    (_ : ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2
      → IsAdmissibleOpponent G J' Fa zbB ((2 : ℝ) * ((2 : ℝ) * (cc + (↑K₀ : ℝ)) + Cga) +
      (4 : ℝ)) ∧ HasDepthEnergy G J' Fa zbB ((2 : ℝ) * ((2 : ℝ) * (cc + (↑K₀ : ℝ)) +
      Cga) + (4 : ℝ)))
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J Sa.Nc ∧ Sa.tree.seg I = Ka ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G R.1 R.2)
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J Sb.Nc ∧ Sb.tree.seg I = Kb ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G R.1 R.2)
    (_ : IntegrableOn (fun (y : ℝ) => ‖Fa y‖ ^ (2 : ℕ)) (dyadicGridCell G R.1 R.2) volume),
  ∑ I ∈ T, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1) (w
    I) (slots4 a i k (f a - ga I) (Xi.val I) (Xk.val I) (f b - gb I)) -
    localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (Sa.phys I
    (Sa.tree.st I).1 (Sa.tree.st I).2 - ga I) (Xi.val I) (Xk.val I) (Sb.phys I
    (Sb.tree.st I).1 (Sb.tree.st I).2 - gb I))‖ ≤ (↑(Fintype.card Xi.Λ) : ℝ) *
    (↑(Fintype.card Xk.Λ) : ℝ) * (Ea * ((2 : ℝ) * ((1 : ℝ) + Cgb) + (4 : ℝ))) * √(∫ (y
    : ℝ) in dyadicGridCell G R.1 R.2, ‖(↑(↑Sa.input : ℝ →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2
    : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2, ‖Fb y‖ ^ (2 : ℕ)) +
    (↑(Fintype.card Xi.Λ) : ℝ) * (↑(Fintype.card Xk.Λ) : ℝ) * (Eb * ((2 : ℝ) * ((2 :
    ℝ) * (cc + (↑K₀ : ℝ)) + Cga) + (4 : ℝ))) * √(∫ (y : ℝ) in dyadicGridCell G R.1
    R.2, ‖(↑(↑Sb.input : ℝ →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in
    dyadicGridCell G R.1 R.2, ‖Fa y‖ ^ (2 : ℕ))




private theorem replaceTuple_hcell : ReplaceTupleHcellStatement := by
  classical
  intro κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik hib hkb K₀ Ma Mb f
    w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb R hR ga gb zga zgb Cga Cgb hgam hgbm hzga hzgb T hT Sa Sb
    htha Fb hFb hfam hfbm zbA hzbA hzbAm hzbA2 zPa hzPa zbB hzbB hzbBm hzbB2 I hI
  obtain ⟨hIc, hsa, hsb, hIR, hga_ae, hgb_ae⟩ := hT I hI
  have hr := dyadicGridLength_pos G I.1
  have hwI := hw I
  set! μI := normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
  have hprob : IsProbabilityMeasure μI := normalizedIntervalMeasure_probability _ hr
  have hIT : I ∈ dyadicFiniteTree G J N := AccSetup.coarse_tree hSa hIc
  have hIJ : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2 :=
    ((dyadicFiniteTree_mem_iff G J I N).mp hIT).1
  have hfaf : eLpNorm (f a) 2 μI ≠ ⊤ := hSa.f_fin hIT
  have hfbf : eLpNorm (f b) 2 μI ≠ ⊤ := hSb.f_fin hIT
  have hXim := Xi.val_measurable I
  have hXkm := Xk.val_measurable I
  have hXif : eLpNorm (Xi.val I) 2 μI ≠ ⊤ := (MemLp.of_bound (p := 2) hXim.aestronglyMeasurable
    _ (Filter.Eventually.of_forall (LowList.val_bound Xi I))).eLpNorm_ne_top
  have hXkf : eLpNorm (Xk.val I) 2 μI ≠ ⊤ := (MemLp.of_bound (p := 2) hXkm.aestronglyMeasurable
    _ (Filter.Eventually.of_forall (LowList.val_bound Xk I))).eLpNorm_ne_top
  have hgaf : eLpNorm (ga I) 2 μI ≠ ⊤ := by
    have hae : zga I =ᵐ[μI] ga I := ae_normalized_of_cell hga_ae
    rw [← eLpNorm_congr_ae hae]
    exact (memLp_normalized_of_cell (hzga.1 I).2).eLpNorm_ne_top
  have hgbf : eLpNorm (gb I) 2 μI ≠ ⊤ := by
    have hae : zgb I =ᵐ[μI] gb I := ae_normalized_of_cell hgb_ae
    rw [← eLpNorm_congr_ae hae]
    exact (memLp_normalized_of_cell (hzgb.1 I).2).eLpNorm_ne_top
  set Pa := Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 with hPa
  set Pb := Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 with hPb
  have hPam : Measurable Pa := Sa.phys_measurable _ _ _
  have hPbm : Measurable Pb := Sb.phys_measurable _ _ _
  have hPaf : eLpNorm Pa 2 μI ≠ ⊤ := Sa.phys_fin I _ _
  have hPbf : eLpNorm Pb 2 μI ≠ ⊤ := Sb.phys_fin I _ _
  have hzbAf : eLpNorm (zbA I) 2 μI ≠ ⊤ := (memLp_normalized_of_cell (hzbA2 I)).eLpNorm_ne_top
  have hzbBf : eLpNorm (zbB I) 2 μI ≠ ⊤ := (memLp_normalized_of_cell (hzbB2 I)).eLpNorm_ne_top
  have hAae : zbA I =ᵐ[μI] f b - gb I := by
    refine ae_normalized_of_cell ?_
    filter_upwards [hgb_ae] with y hy hyI
    simp only [hzbA, Pi.sub_apply]
    rw [hy hyI, hFb, Set.indicator_of_mem (hIJ hyI)]
    ring
  have hBae : zbB I =ᵐ[μI] Pa - ga I := by
    refine ae_normalized_of_cell ?_
    obtain ⟨-, hIKa, -, -⟩ := htha.seg_spec hIc
    rw [hsa] at hIKa
    have hIRb : I ∈ pathBelow G J N R := (PathColumnSystem.below_mem_iff hR I).mpr ⟨hIT, hIR⟩
    have hdel := hSa.system_delayed_ae hR hIRb hIc hIKa
      (dyadicGridCell_depth_le_of_subset G I Ka hIKa)
    have hshallow : I.1 + K₀ ≤ J.1 + N := by
      have hm : I.1 ≤ J.1 + ((N - K₀ : ℕ) : ℤ) := ((dyadicFiniteTree_mem_iff G J I _).mp hIc).2
      have h1 : K₀ ≤ N := hSa.K₀_le
      have h2 : ((N - K₀ : ℕ) : ℤ) = (N : ℤ) - K₀ := by push_cast [h1]; ring
      omega
    have hst : Sa.tree.st I = (fitState G Ma Sa.P Sa.O (I.1 - Ka.1).toNat I) := by
      change Sa.tree.state (Sa.tree.depthIn I) I = _
      unfold GreedyTree.depthIn GreedyTree.state
      rw [hsa]
      rfl
    filter_upwards [hdel, hga_ae] with y hy hy' hyI
    simp only [hzbB, hzPa, hshallow, ↓reduceIte, Pi.sub_apply]
    have e : ((Sa.system Ka).family R hR).delayed Sa.input K₀ I y = Pa y := by
      rw [hPa, hst]; exact hy hyI
    rw [e, hy' hyI]
    ring
  have hXbf : eLpNorm (f b - gb I) 2 μI ≠ ⊤ := ((eLpNorm_sub_le (by norm_num)).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hfbf.lt_top, hgbf.lt_top⟩)).ne
  have e1 := localProgressionForm_slots4_sub_common hr hwI hai hak hab hik hib hkb hfam hPam
    (hgam I) hXim hXkm (hfbm.sub (hgbm I)) hfaf hPaf hgaf hXif hXkf hXbf
  have e2 := localProgressionForm_slots4_congr_b hr hwI hai hak hab hik hib hkb hfam hXim hXkm
    (hzbAm I) (hfbm.sub (hgbm I)) hfaf hXif hXkf hzbAf hXbf hAae
  have e3 := localProgressionForm_slots4_congr_b hr hwI hai hak hab hik hib hkb hPam hXim hXkm
    (hzbAm I) (hfbm.sub (hgbm I)) hPaf hXif hXkf hzbAf hXbf hAae
  have hYaf : eLpNorm (Pa - ga I) 2 μI ≠ ⊤ := ((eLpNorm_sub_le (by norm_num)).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hPaf.lt_top, hgaf.lt_top⟩)).ne
  have e4 := localProgressionForm_slots4_sub_common hr hwI hib.symm hkb.symm hab.symm hik
    hai.symm hak.symm hfbm hPbm (hgbm I) hXim hXkm (hPam.sub (hgam I)) hfbf hPbf hgbf hXif hXkf
    hYaf
  have e5 := localProgressionForm_slots4_congr_b hr hwI hib.symm hkb.symm hab.symm hik hai.symm
    hak.symm hfbm hXim hXkm (hzbBm I) (hPam.sub (hgam I)) hfbf hXif hXkf hzbBf hYaf hBae
  have e6 := localProgressionForm_slots4_congr_b hr hwI hib.symm hkb.symm hab.symm hik hai.symm
    hak.symm hPbm hXim hXkm (hzbBm I) (hPam.sub (hgam I)) hPbf hXif hXkf hzbBf hYaf hBae
  have hsw1 := slots4_swap hai hak hab hik hib hkb (Pa - ga I) (Xi.val I) (Xk.val I)
    (f b - gb I)
  have hsw2 := slots4_swap hai hak hab hik hib hkb (Pa - ga I) (Xi.val I) (Xk.val I)
    (Pb - gb I)
  have hsplit : localProgressionForm (dyadicGridLength G I.1) (w I)
        (slots4 a i k (f a - ga I) (Xi.val I) (Xk.val I) (f b - gb I)) -
      localProgressionForm (dyadicGridLength G I.1) (w I)
        (slots4 a i k (Pa - ga I) (Xi.val I) (Xk.val I) (Pb - gb I)) =
      (localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (f a) (Xi.val I) (Xk.val I) (zbA I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k Pa (Xi.val I) (Xk.val I) (zbA I))) +
      (localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 b i k (f b) (Xi.val I) (Xk.val I) (zbB I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 b i k Pb (Xi.val I) (Xk.val I) (zbB I))) := by
    rw [e2, e3, e5, e6, ← e1, ← e4, ← hsw1, ← hsw2]
    ring
  rw [hsplit]
  exact norm_add_le _ _



private theorem replaceTuple_stage_1 : ReplaceTupleStage1Statement := by
  classical
  intro κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik hib hkb hD1 K₀ Ma
    Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb hKa hKb R hR ga gb zga zgb Cga Cgb hCga hCgb hgam
    hgbm hzga hzgb T hT Sa Sb Ea Eb htha Fa Fb hFb hfam hfbm hFbL zbA hzbA hzbAm hzbA2 hzbAJ zPa
    hzPa cc hcc hcc0 zbB hzbB hzbBm hzbB2 hzbBJ hTa hTb hFaR
  have hFbR : IntegrableOn (fun y => ‖Fb y‖ ^ 2) (dyadicGridCell G R.1 R.2) :=
    (hFbL.integrable_norm_pow two_ne_zero).integrableOn
  have hrepA := replaceSlot κ Xi Xk a i k b Bp D pkga hε0 hε1 hai hak hab hik hib hkb hD1 K₀ Ma
    (f a) w q ka c₂ Ba hSa hw hKa hR T hTa (by positivity) hzbAJ hzbAm hzbA2 hFbR
  have hrepB := replaceSlot κ Xi Xk b i k a Bp D pkgb hε0 hε1 hib.symm hkb.symm hab.symm hik
    hai.symm hak.symm hD1 K₀ Mb (f b) w q kb c₂ Bb hSb hw hKb hR T hTb (by positivity) hzbBJ
    hzbBm hzbB2 hFaR
  -- the per-cell decomposition
  have hcell : ∀ I ∈ T,
      ‖localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (f a - ga I) (Xi.val I) (Xk.val I) (f b - gb I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 - ga I) (Xi.val I)
            (Xk.val I) (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 - gb I))‖ ≤
      ‖localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (f a) (Xi.val I) (Xk.val I) (zbA I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2) (Xi.val I) (Xk.val I)
            (zbA I))‖ +
      ‖localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 b i k (f b) (Xi.val I) (Xk.val I) (zbB I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 b i k (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2) (Xi.val I) (Xk.val I)
            (zbB I))‖ := by
    expose_names
    exact @replaceTuple_hcell κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab
      hik hib hkb K₀ Ma Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb R hR ga gb zga zgb Cga Cgb hgam
      hgbm hzga hzgb T hT htha hFb hfam hfbm hzbA hzbAm hzbA2 hzPa hzbB hzbBm hzbB2
  calc _ ≤ ∑ I ∈ T, (dyadicGridLength G I.1 *
        ‖localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 a i k (f a) (Xi.val I) (Xk.val I) (zbA I)) -
          localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2) (Xi.val I) (Xk.val I)
              (zbA I))‖ +
        dyadicGridLength G I.1 *
        ‖localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 b i k (f b) (Xi.val I) (Xk.val I) (zbB I)) -
          localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 b i k (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2) (Xi.val I) (Xk.val I)
              (zbB I))‖) := Finset.sum_le_sum fun I hI => by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hcell I hI) (dyadicGridLength_pos G I.1).le
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by
        refine add_le_add (hrepA.trans (le_of_eq ?_)) (hrepB.trans (le_of_eq ?_))
        · simp only [Ea]; ring
        · simp only [Eb, hcc]; ring


/-- Blueprint prop:base, proof lines 1626-1641 (eq:Y): on the cells of a common root `R` inside
the accurate-fit roots `K_a, K_b`, the tuple `(X_i, X_k, f_a - g_a, f_b - g_b)` is replaced by
`(X_i, X_k, P_a - g_a, P_b - g_b)` with the delayed physical projections of the accurate fits,
first in slot `a` (opponent `f_b - g_b`) and then in slot `b` (delayed opponent `P_a - g_a`). -/
theorem replaceTuple (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b)
    (hkb : k ≠ b) (hD1 : 1 ≤ D) (K₀ Ma Mb : ℕ) (f : Fin 4 → ℝ → ℂ) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (q : ℝ) (ka kb c₂ : ℕ) (Ba Bb : ℝ)
    (hSa : (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).Hyp)
    (hSb : (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).Hyp)
    (hw : ∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
      (w I))
    {Ka Kb : ℤ × ℤ}
    (hKa : Ka ∈ (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      Ba).tree.roots)
    (hKb : Kb ∈ (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      Bb).tree.roots)
    {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N)
    (ga gb zga zgb : ℤ × ℤ → ℝ → ℂ) {Cga Cgb : ℝ} (hCga : 0 ≤ Cga) (hCgb : 0 ≤ Cgb)
    (hgam : ∀ I, Measurable (ga I)) (hgbm : ∀ I, Measurable (gb I))
    (hzga : (∀ I, Measurable (zga I) ∧ MemLp (zga I) 2 (volume.restrict (dyadicGridCell G I.1
        I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f a) zga Cga ∧ HasDepthEnergy G J' (f a) zga 1)
    (hzgb : (∀ I, Measurable (zgb I) ∧ MemLp (zgb I) 2 (volume.restrict (dyadicGridCell G I.1
        I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f b) zgb Cgb ∧ HasDepthEnergy G J' (f b) zgb 1)
    (T : Finset (ℤ × ℤ))
    (hT : ∀ I ∈ T, I ∈ dyadicFiniteTree G J
        (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).Nc ∧
      (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.seg I = Ka ∧
      (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.seg I = Kb ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zga I y = ga I y) ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zgb I y = gb I y)) :
    let Sa := predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba
    let Sb := predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb
    let Ea := 2 * Real.exp (-Bp) * (2 * (compressionOneConst ((Sa.system Ka).rooted R) + K₀) + 1)
      + D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)
    let Eb := 2 * Real.exp (-Bp) * (2 * (compressionOneConst ((Sb.system Kb).rooted R) + K₀) + 1)
      + D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)
    ∑ I ∈ T, dyadicGridLength G I.1 *
      ‖localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (f a - ga I) (Xi.val I) (Xk.val I) (f b - gb I)) -
        localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 - ga I) (Xi.val I)
            (Xk.val I) (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 - gb I))‖ ≤
      (Fintype.card Xi.Λ * Fintype.card Xk.Λ) * (Ea * (2 * (1 + Cgb) + 4)) *
          Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(Sa.input : ℝ → ℂ) y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G R.1 R.2,
            ‖(dyadicGridCell G J.1 J.2).indicator (f b) y‖ ^ 2) +
        (Fintype.card Xi.Λ * Fintype.card Xk.Λ) *
          (Eb * (2 * (2 * (compressionOneConst ((Sa.system Ka).rooted R) + K₀) + Cga) + 4)) *
          Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(Sb.input : ℝ → ℂ) y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G R.1 R.2,
            ‖(dyadicGridCell G J.1 J.2).indicator (f a) y‖ ^ 2) := by
  intro Sa Sb Ea Eb
  classical
  have htha := hSa.treeHyp
  have hthb := hSb.treeHyp
  set Fa := (dyadicGridCell G J.1 J.2).indicator (f a) with hFa
  set Fb := (dyadicGridCell G J.1 J.2).indicator (f b) with hFb
  have hJT : J ∈ dyadicFiniteTree G J N := dyadicFiniteTree_root_mem G J N
  have hrJ := dyadicGridLength_pos G J.1
  have hfam : Measurable (f a) := hSa.f_meas
  have hfbm : Measurable (f b) := hSb.f_meas
  have hfaJ : MemLp (f a) 2 (volume.restrict (dyadicGridCell G J.1 J.2)) := by
    have hN : eLpNorm (f a) 2 (normalizedIntervalMeasure (dyadicGridLeft G J.1 J.2)
        (dyadicGridLength G J.1)) ≤ 1 := hSa.f_norm_root
    exact memLp_restrict_of_normalized hrJ
      (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top hN))
  have hfbJ : MemLp (f b) 2 (volume.restrict (dyadicGridCell G J.1 J.2)) := by
    have hN : eLpNorm (f b) 2 (normalizedIntervalMeasure (dyadicGridLeft G J.1 J.2)
        (dyadicGridLength G J.1)) ≤ 1 := hSb.f_norm_root
    exact memLp_restrict_of_normalized hrJ
      (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top hN))
  have hFaL : MemLp Fa 2 volume :=
    (memLp_indicator_iff_restrict (dyadicGridCell_measurable _ _ _)).mpr hfaJ
  have hFbL : MemLp Fb 2 volume :=
    (memLp_indicator_iff_restrict (dyadicGridCell_measurable _ _ _)).mpr hfbJ
  have hFam : Measurable Fa := hfam.indicator (dyadicGridCell_measurable _ _ _)
  have hFbm : Measurable Fb := hfbm.indicator (dyadicGridCell_measurable _ _ _)
  have henergy : ∀ (l : ℝ → ℂ) (J' : ℤ × ℤ), J' ∈ dyadicFiniteTree G J N →
      ∫ y in dyadicGridCell G J'.1 J'.2, ‖l y‖ ^ 2 =
        ∫ y in dyadicGridCell G J'.1 J'.2, ‖(dyadicGridCell G J.1 J.2).indicator l y‖ ^ 2 := by
    intro l J' hJ'
    have hJ'J := ((dyadicFiniteTree_mem_iff G J J' N).mp hJ').1
    refine setIntegral_congr_fun (dyadicGridCell_measurable _ _ _) fun y hy => ?_
    simp only [Set.indicator_of_mem (hJ'J hy)]
  -- the opponent of the slot-`a` replacement: `F_b - g_b`
  set! zbA : ℤ × ℤ → ℝ → ℂ := fun I y => Fb y + -zgb I y with hzbA
  have hzbAm : ∀ I, Measurable (zbA I) := fun I => hFbm.add (hzgb.1 I).1.neg
  have hzbA2 : ∀ I, MemLp (zbA I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)) := fun I =>
    (hFbL.restrict _).add (hzgb.1 I).2.neg
  have hzbAJ : ∀ J' ∈ dyadicFiniteTree G J N,
      dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
      IsAdmissibleOpponent G J' Fb zbA (2 * (1 + Cgb) + 4) ∧
        HasDepthEnergy G J' Fb zbA (2 * (1 + Cgb) + 4) := by
    intro J' hJ' hJ'R
    obtain ⟨h1, h2⟩ := hzgb.2 J' hJ' hJ'R
    have hE := henergy (f b) J' hJ'
    have hfix := isAdmissibleOpponent_fixed G J' (F := Fb)
      (hFbL.indicator (dyadicGridCell_measurable _ _ _))
    have hfixE := hasDepthEnergy_fixed G J' (F := Fb)
      ((hFbL.integrable_norm_pow two_ne_zero).integrableOn)
    have hfit := (isAdmissibleOpponent_congr h1 (fun _ _ => rfl) hE).neg
    have hfitE := (hasDepthEnergy_congr h2 (fun _ _ => rfl) hE).neg
    have hadd := IsAdmissibleOpponent.add zero_le_one hCgb hfix hfit
      (fun I => hFbL.restrict _) (fun I => (hzgb.1 I).2.neg)
    have haddE := HasDepthEnergy.add zero_le_one zero_le_one hfixE hfitE
      (fun I => hFbL.restrict _) (fun I => (hzgb.1 I).2.neg)
    exact ⟨hadd.mono (by positivity) (by linarith), haddE.mono (by norm_num) (by linarith)⟩
  -- the opponent of the slot-`b` replacement: `P_a - g_a` (delayed)
  obtain ⟨hzPm, hzPadm⟩ := (Sa.system Ka).delayed_opponent hR Sa.input K₀
  set! zPa : ℤ × ℤ → ℝ → ℂ := fun I =>
    if I.1 + K₀ ≤ J.1 + N then ((Sa.system Ka).family R hR).delayed Sa.input K₀ I else 0
    with hzPa
  set cc := compressionOneConst ((Sa.system Ka).rooted R) with hcc
  have hcc0 : 0 ≤ cc := by
    rw [hcc]; unfold compressionOneConst
    have := ((Sa.system Ka).rooted R).two_le_budget
    have : 0 ≤ Real.log (2 * ((Sa.system Ka).rooted R).budget) := Real.log_nonneg (by linarith)
    positivity
  set! zbB : ℤ × ℤ → ℝ → ℂ := fun I y => zPa I y + -zga I y with hzbB
  have hzbBm : ∀ I, Measurable (zbB I) := fun I => (hzPm I).1.add (hzga.1 I).1.neg
  have hzbB2 : ∀ I, MemLp (zbB I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)) := fun I =>
    (hzPm I).2.add (hzga.1 I).2.neg
  have hinJ : ∀ J' ∈ dyadicFiniteTree G J N,
      ∫ y in dyadicGridCell G J'.1 J'.2, ‖(Sa.input : ℝ → ℂ) y‖ ^ 2 =
        ∫ y in dyadicGridCell G J'.1 J'.2, ‖Fa y‖ ^ 2 := by
    intro J' hJ'
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' (dyadicGridCell_measurable _ _ _)]
    filter_upwards [hSa.input_ae] with y hy _
    rw [hy]
    rfl
  have hzbBJ : ∀ J' ∈ dyadicFiniteTree G J N,
      dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
      IsAdmissibleOpponent G J' Fa zbB (2 * (2 * (cc + K₀) + Cga) + 4) ∧
        HasDepthEnergy G J' Fa zbB (2 * (2 * (cc + K₀) + Cga) + 4) := by
    intro J' hJ' hJ'R
    obtain ⟨h1, h2⟩ := hzga.2 J' hJ' hJ'R
    obtain ⟨hP1, hP2⟩ := hzPadm J' hJ' hJ'R
    have hE := henergy (f a) J' hJ'
    have hPa := isAdmissibleOpponent_congr hP1 (fun _ _ => rfl) (hinJ J' hJ')
    have hPaE := hasDepthEnergy_congr hP2 (fun _ _ => rfl) (hinJ J' hJ')
    have hfit := (isAdmissibleOpponent_congr h1 (fun _ _ => rfl) hE).neg
    have hfitE := (hasDepthEnergy_congr h2 (fun _ _ => rfl) hE).neg
    have hadd := IsAdmissibleOpponent.add (by positivity) hCga hPa hfit
      (fun I => (hzPm I).2) (fun I => (hzga.1 I).2.neg)
    have haddE := HasDepthEnergy.add zero_le_one zero_le_one hPaE hfitE
      (fun I => (hzPm I).2) (fun I => (hzga.1 I).2.neg)
    exact ⟨hadd.mono (by positivity) (by linarith), haddE.mono (by norm_num) (by
      have : 0 ≤ 2 * (2 * (cc + K₀) + Cga) := by positivity
      linarith)⟩
  -- the two replacements
  have hTa : ∀ I ∈ T, I ∈ dyadicFiniteTree G J Sa.Nc ∧ Sa.tree.seg I = Ka ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 := fun I hI =>
    ⟨(hT I hI).1, (hT I hI).2.1, (hT I hI).2.2.2.1⟩
  have hTb : ∀ I ∈ T, I ∈ dyadicFiniteTree G J Sb.Nc ∧ Sb.tree.seg I = Kb ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 := fun I hI =>
    ⟨(hT I hI).1, (hT I hI).2.2.1, (hT I hI).2.2.2.1⟩
  have hFaR : IntegrableOn (fun y => ‖Fa y‖ ^ 2) (dyadicGridCell G R.1 R.2) :=
    (hFaL.integrable_norm_pow two_ne_zero).integrableOn
  expose_names
  exact @replaceTuple_stage_1 κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab
    hik hib hkb hD1 K₀ Ma Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb hKa hKb R hR ga gb zga zgb Cga
    Cgb hCga hCgb hgam hgbm hzga hzgb T hT htha hFb hfam hfbm hFbL hzbA hzbAm hzbA2 hzbAJ hzPa hcc
    hcc0 hzbB hzbBm hzbB2 hzbBJ hTa hTb hFaR

end ReplaceTuple

/-- Blueprint eq:min-subadd (line 1659). -/
theorem min_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ j ∈ s, 0 ≤ a j) {η : ℝ}
    (hη : 0 ≤ η) : min η (∑ j ∈ s, a j) ≤ ∑ j ∈ s, min η (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hη]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have ih' := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hai := ha i (Finset.mem_insert_self _ _)
    have hs : 0 ≤ ∑ j ∈ s, min η (a j) :=
      Finset.sum_nonneg fun j hj => le_min hη (ha j (Finset.mem_insert_of_mem hj))
    rcases le_total η (a i) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right hs)
    · rw [min_eq_right h]
      calc min η (a i + ∑ j ∈ s, a j) ≤ a i + min η (∑ j ∈ s, a j) := by
            rcases le_total η (∑ j ∈ s, a j) with h' | h'
            · rw [min_eq_left h']
              exact (min_le_left _ _).trans (by
                have := min_le_left η (∑ j ∈ s, a j); rw [min_eq_left h'] at this; linarith)
            · rw [min_eq_right h']
              exact min_le_right _ _
        _ ≤ _ := by linarith

/-- The cell sum weighted by length is the integral over the root of the path sums. -/
theorem cells_sum_eq_integral (G : RealDyadicGrid) (cells : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℝ) :
    ∑ I ∈ cells, dyadicGridLength G I.1 * f I =
      ∫ y, ∑ I ∈ cells, Set.indicator (dyadicGridCell G I.1 I.2) (fun _ => f I) y := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun I _ => ?_
    rw [integral_indicator_const _ (dyadicGridCell_measurable _ _ _), measureReal_def,
      dyadicGridCell_volume, ENNReal.toReal_ofReal (dyadicGridLength_pos G I.1).le, smul_eq_mul]
  · intro I _
    exact ((continuous_const.integrableOn_Icc).mono_set
        Set.Ico_subset_Icc_self).integrable_indicator
      (dyadicGridCell_measurable _ _ _)

open scoped Classical in
/-- Path bounds integrate to a root bound: if every path through the root collects at most `M`,
the length-weighted cell sum is at most `M |R|`. -/
theorem cells_sum_le_of_path (G : RealDyadicGrid) (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    {f : ℤ × ℤ → ℝ} (hf : ∀ I, 0 ≤ f I) {M : ℝ}
    (hM : ∀ y, ∑ I ∈ cells with y ∈ dyadicGridCell G I.1 I.2, f I ≤ M) :
    ∑ I ∈ cells, dyadicGridLength G I.1 * f I ≤ dyadicGridLength G R.1 * M := by
  rw [cells_sum_eq_integral]
  have hM0 : 0 ≤ M := by
    have := hM (dyadicGridLeft G R.1 R.2 - 1 - dyadicGridLength G R.1)
    exact (Finset.sum_nonneg fun I _ => hf I).trans this
  have hpt : ∀ y, ∑ I ∈ cells, Set.indicator (dyadicGridCell G I.1 I.2) (fun _ => f I) y ≤
      Set.indicator (dyadicGridCell G R.1 R.2) (fun _ => M) y := by
    intro y
    have he : ∑ I ∈ cells, Set.indicator (dyadicGridCell G I.1 I.2) (fun _ => f I) y =
        ∑ I ∈ cells with y ∈ dyadicGridCell G I.1 I.2, f I := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun I _ => ?_
      by_cases hy : y ∈ dyadicGridCell G I.1 I.2
      · rw [Set.indicator_of_mem hy]; simp only [hy, ↓reduceIte]
      · rw [Set.indicator_of_notMem hy]; simp only [hy, ↓reduceIte]
    rw [he]
    by_cases hyR : y ∈ dyadicGridCell G R.1 R.2
    · rw [Set.indicator_of_mem hyR]; exact hM y
    · rw [Set.indicator_of_notMem hyR]
      refine le_of_eq (Finset.sum_eq_zero fun I hI => ?_)
      exact absurd (hsub I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2) hyR
  calc _ ≤ ∫ y, Set.indicator (dyadicGridCell G R.1 R.2) (fun _ => M) y := by
        refine integral_mono ?_ ?_ hpt
        · exact integrable_finsetSum _ fun I _ =>
            ((continuous_const.integrableOn_Icc).mono_set
                Set.Ico_subset_Icc_self).integrable_indicator
              (dyadicGridCell_measurable _ _ _)
        · exact ((continuous_const.integrableOn_Icc).mono_set
            Set.Ico_subset_Icc_self).integrable_indicator
            (dyadicGridCell_measurable _ _ _)
    _ = dyadicGridLength G R.1 * M := by
        rw [integral_indicator_const _ (dyadicGridCell_measurable _ _ _), measureReal_def,
          dyadicGridCell_volume, ENNReal.toReal_ofReal (dyadicGridLength_pos G R.1).le, smul_eq_mul]

/-- The data of the active-cell reduction (blueprint prop:base, lines 1655-1660): on the cells
below a root, the four arguments `Y_l = B_l + U_l` with `U_i = U_j = 0`, where the basic
arguments `B_l` are combinations of bounded atoms which, along each path, are fixed quadratic
chart atoms of bounded complexity, and every cell has `|H_I(Y)| ≤ η`. -/
structure ActiveSetup (κ : LocalKernelClass) (c₀ : ℕ) where
  /-- Dyadic grid supporting the active setup. -/
  G : RealDyadicGrid
  /-- Root cell containing all active-setup cells. -/
  R : ℤ × ℤ
  /-- Finite collection of cells used in the active reduction. -/
  cells : Finset (ℤ × ℤ)
  sub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2
  /-- Admissible local kernel assigned to each active-setup cell. -/
  w : ℤ × ℤ → ℝ × ℝ → ℂ
  adm : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
    (w I)
  /-- Finite label type for the pathwise quadratic-chart atoms. -/
  L : Type
  [fin : Fintype L]
  /-- Bounded measurable scalar atom at each cell and label. -/
  φ : ℤ × ℤ → L → ℝ → ℂ
  φ_meas : ∀ I v, Measurable (φ I v)
  φ_bound : ∀ I v x, ‖φ I v x‖ ≤ 1
  /-- Uniform complexity budget for the pathwise charts. -/
  H : ℝ
  /-- Coefficient of each chart atom in each slot and cell. -/
  coef : Fin 4 → ℤ × ℤ → L → ℂ
  path_chart : ∀ y v, ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀ H B ∧
    IsBoundedQuadraticChart B ∧ ∀ I ∈ cells, y ∈ dyadicGridCell G I.1 I.2 →
      (∃ l, coef l I v ≠ 0) → ∀ x ∈ dyadicGridCell G I.1 I.2, φ I v x = quadraticChartAtom B x
  nested_chart : ∀ I ∈ cells, ∀ v, (∃ l, coef l I v ≠ 0) → ∃ (d : ℕ) (B : QuadraticChartData d),
    QuadraticChartComplexity c₀ H B ∧ IsBoundedQuadraticChart B ∧ φ I v = quadraticChartAtom B
  nested_cons : ∀ I ∈ cells, ∀ I' ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 →
    ∀ v, (∃ l, coef l I v ≠ 0) → (∃ l, coef l I' v ≠ 0) → φ I v = φ I' v
  /-- Uniform bound for the chart coefficients. -/
  Dc : ℝ
  Dc_nonneg : 0 ≤ Dc
  coef_le : ∀ l I v, ‖coef l I v‖ ≤ Dc
  /-- First slot allowed to carry an additional L² error term. -/
  a : Fin 4
  /-- Second slot allowed to carry an additional L² error term. -/
  b : Fin 4
  hab : a ≠ b
  /-- Additional measurable L² error terms in the two distinguished slots. -/
  U : Fin 4 → ℤ × ℤ → ℝ → ℂ
  U_meas : ∀ l I, Measurable (U l I)
  /-- Uniform normalized L² norm bound for the additional error terms. -/
  S : ℝ
  U_L2 : ∀ l I, MemLp (U l I) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
    (dyadicGridLength G I.1))
  U_le : ∀ l I, (eLpNorm (U l I) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
    (dyadicGridLength G I.1))).toReal ≤ S
  /-- Upper bound for the norm of the four-linear local form at each cell. -/
  η : ℝ
  small : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
    (fun l => (fun x => ∑ v, coef l I v * φ I v x) +
      if l = a ∨ l = b then U l I else 0)‖ ≤ η

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)

attribute [instance] ActiveSetup.fin

/-- The normalized measure of a cell. -/
noncomputable abbrev μ (I : ℤ × ℤ) : Measure ℝ :=
  normalizedIntervalMeasure (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)

/-- The local form on a cell. -/
noncomputable abbrev Hf (I : ℤ × ℤ) (F : Fin 4 → ℝ → ℂ) : ℂ :=
  localProgressionForm (dyadicGridLength A.G I.1) (A.w I) F

/-- The basic arguments. -/
noncomputable def B (l : Fin 4) (I : ℤ × ℤ) : ℝ → ℂ := fun x => ∑ v, A.coef l I v * A.φ I v x

/-- The patterns: `0` all basic, `1` the side `U_a`, `2` the side `U_b`, `3` both sides. -/
noncomputable def z (p : Fin 4) (I : ℤ × ℤ) : Fin 4 → ℝ → ℂ :=
  match p with
  | 0 => fun l => A.B l I
  | 1 => Function.update (fun l => A.B l I) A.a (A.U A.a I)
  | 2 => Function.update (fun l => A.B l I) A.b (A.U A.b I)
  | 3 => Function.update (Function.update (fun l => A.B l I) A.a (A.U A.a I)) A.b (A.U A.b I)

/-- The slot carrying the possibly non-basic argument of the patterns `0, 1, 2`. -/
def mslot (p : Fin 3) : Fin 4 := if p = 2 then A.b else A.a

theorem B_meas (l : Fin 4) (I : ℤ × ℤ) : Measurable (A.B l I) :=
  Finset.measurable_sum _ fun v _ => measurable_const.mul (A.φ_meas I v)

theorem B_bound (l : Fin 4) (I : ℤ × ℤ) (x : ℝ) :
    ‖A.B l I x‖ ≤ Fintype.card A.L * A.Dc := by
  unfold B
  refine (norm_sum_le _ _).trans ?_
  calc ∑ v, ‖A.coef l I v * A.φ I v x‖ ≤ ∑ _v : A.L, A.Dc := Finset.sum_le_sum fun v _ => by
        rw [norm_mul]
        have h0 : 0 ≤ ‖A.coef l I v‖ := norm_nonneg _
        calc ‖A.coef l I v‖ * ‖A.φ I v x‖ ≤ ‖A.coef l I v‖ * 1 :=
              mul_le_mul_of_nonneg_left (A.φ_bound I v x) h0
          _ ≤ A.Dc := by rw [mul_one]; exact A.coef_le l I v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem B_memLp (l : Fin 4) (I : ℤ × ℤ) : MemLp (A.B l I) 2 (A.μ I) := by
  have : IsProbabilityMeasure (A.μ I) :=
    normalizedIntervalMeasure_probability _ (dyadicGridLength_pos A.G I.1)
  exact MemLp.of_bound (A.B_meas l I).aestronglyMeasurable _
    (Filter.Eventually.of_forall (A.B_bound l I))

theorem B_eLpNorm_le (l : Fin 4) (I : ℤ × ℤ) :
    (eLpNorm (A.B l I) 2 (A.μ I)).toReal ≤ Fintype.card A.L * A.Dc := by
  have hprob : IsProbabilityMeasure (A.μ I) :=
    normalizedIntervalMeasure_probability _ (dyadicGridLength_pos A.G I.1)
  have hC : 0 ≤ (Fintype.card A.L : ℝ) * A.Dc := (norm_nonneg _).trans (A.B_bound l I 0)
  have h : eLpNorm (A.B l I) 2 (A.μ I) ≤ ENNReal.ofReal ((Fintype.card A.L : ℝ) * A.Dc) :=
    (eLpNorm_le_of_ae_bound (A.B_meas l I).aestronglyMeasurable
      (Filter.Eventually.of_forall (A.B_bound l I))).trans (by simp)
  calc (eLpNorm (A.B l I) 2 (A.μ I)).toReal ≤ (ENNReal.ofReal ((Fintype.card A.L : ℝ) *
        A.Dc)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = _ := ENNReal.toReal_ofReal hC

/-- The replaced tuple `Y_l = B_l + U_l` with `U_i = U_j = 0`. -/
noncomputable def Y (I : ℤ × ℤ) : Fin 4 → ℝ → ℂ :=
  fun l => A.B l I + if l = A.a ∨ l = A.b then A.U l I else 0

/-- The transpose norm of an atom triple in the slots other than `m`. -/
noncomputable def tnorm (I : ℤ × ℤ) (m : Fin 4) (v₀ v₁ v₂ : A.L) : ℝ :=
  transposeNorm (dyadicGridLength A.G I.1) (A.w I) m
    (tripleSlots 0 m ![A.φ I v₀, A.φ I v₁, A.φ I v₂])

theorem tnorm_nonneg (I : ℤ × ℤ) (m : Fin 4) (v₀ v₁ v₂ : A.L) : 0 ≤ A.tnorm I m v₀ v₁ v₂ :=
  transposeNorm_nonneg _ _ _ _

theorem Y_eq (I : ℤ × ℤ) : A.Y I = Function.update (Function.update (fun l => A.B l I) A.a
    (A.B A.a I + A.U A.a I)) A.b (A.B A.b I + A.U A.b I) := by
  funext l
  by_cases hb : l = A.b
  · subst hb; simp [Y]
  · rw [Function.update_of_ne hb]
    by_cases ha : l = A.a
    · subst ha; simp [Y]
    · rw [Function.update_of_ne ha]; simp [Y, ha, hb]

/-- Multilinearity: `H(Y) = Σ_p H(z_p)` over the four patterns. -/
theorem H_Y_eq {I : ℤ × ℤ} (hI : I ∈ A.cells) : A.Hf I (A.Y I) = ∑ p, A.Hf I (A.z p I) := by
  have hr := dyadicGridLength_pos A.G I.1
  have hprob : IsProbabilityMeasure (A.μ I) := normalizedIntervalMeasure_probability _ hr
  set G0 : Fin 4 → ℝ → ℂ := fun l => A.B l I with hG0
  have hBf : ∀ l, eLpNorm (A.B l I) 2 (A.μ I) ≠ ⊤ := fun l => (A.B_memLp l I).eLpNorm_ne_top
  have hUf : ∀ l, eLpNorm (A.U l I) 2 (A.μ I) ≠ ⊤ := fun l => (A.U_L2 l I).eLpNorm_ne_top
  have hw := A.adm I hI
  have hG0m : ∀ j, Measurable (G0 j) := fun j => A.B_meas j I
  have hG0f : ∀ j, eLpNorm (G0 j) 2 (A.μ I) ≠ ⊤ := fun j => hBf j
  have hupd : ∀ (G : Fin 4 → ℝ → ℂ) (k : Fin 4) (g : ℝ → ℂ), (∀ j, Measurable (G j)) →
      (∀ j, eLpNorm (G j) 2 (A.μ I) ≠ ⊤) → Measurable g → eLpNorm g 2 (A.μ I) ≠ ⊤ →
      (∀ j, Measurable (Function.update G k g j)) ∧
        ∀ j, eLpNorm (Function.update G k g j) 2 (A.μ I) ≠ ⊤ := by
    intro G k g hG hGf hg hgf
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = k
      · subst hj; rw [Function.update_self]; exact hg
      · rw [Function.update_of_ne hj]; exact hG j
    · by_cases hj : j = k
      · subst hj; rw [Function.update_self]; exact hgf
      · rw [Function.update_of_ne hj]; exact hGf j
  have hsumf : ∀ l, eLpNorm (A.B l I + A.U l I) 2 (A.μ I) ≠ ⊤ := fun l =>
    ((A.B_memLp l I).add (A.U_L2 l I)).eLpNorm_ne_top
  obtain ⟨hG1m, hG1f⟩ := hupd G0 A.a (A.B A.a I + A.U A.a I) hG0m hG0f
    ((A.B_meas _ _).add (A.U_meas _ _)) (hsumf _)
  obtain ⟨hG2m, hG2f⟩ := hupd G0 A.b (A.U A.b I) hG0m hG0f (A.U_meas _ _) (hUf _)
  rw [Y_eq, Fin.sum_univ_four]
  simp only [Hf, z]
  rw [localProgressionForm_update_add_two hr hw hG1m hG1f A.b (A.B_meas _ _) (A.U_meas _ _)
    (hBf _) (hUf _)]
  have e1 : Function.update (Function.update G0 A.a (A.B A.a I + A.U A.a I)) A.b (A.B A.b I) =
      Function.update G0 A.a (A.B A.a I + A.U A.a I) := by
    rw [show A.B A.b I = Function.update G0 A.a (A.B A.a I + A.U A.a I) A.b by
      rw [Function.update_of_ne (Ne.symm A.hab)], Function.update_eq_self]
  have e2 : Function.update (Function.update G0 A.a (A.B A.a I + A.U A.a I)) A.b (A.U A.b I) =
      Function.update (Function.update G0 A.b (A.U A.b I)) A.a (A.B A.a I + A.U A.a I) :=
    (Function.update_comm A.hab.symm _ _ _).symm
  rw [e1, e2]
  rw [localProgressionForm_update_add_two hr hw hG0m hG0f A.a (A.B_meas _ _) (A.U_meas _ _)
    (hBf _) (hUf _)]
  rw [localProgressionForm_update_add_two hr hw hG2m hG2f A.a (A.B_meas _ _) (A.U_meas _ _)
    (hBf _) (hUf _)]
  have e3 : Function.update G0 A.a (A.B A.a I) = G0 := by
    rw [show A.B A.a I = G0 A.a from rfl, Function.update_eq_self]
  have e4 : Function.update (Function.update G0 A.b (A.U A.b I)) A.a (A.B A.a I) =
      Function.update G0 A.b (A.U A.b I) := by
    rw [show A.B A.a I = Function.update G0 A.b (A.U A.b I) A.a by
      rw [Function.update_of_ne A.hab], Function.update_eq_self]
  have e5 : Function.update (Function.update G0 A.b (A.U A.b I)) A.a (A.U A.a I) =
      Function.update (Function.update G0 A.a (A.U A.a I)) A.b (A.U A.b I) :=
    (Function.update_comm A.hab _ _ _).symm
  rw [e3, e4, e5]
  ring

theorem S_nonneg : 0 ≤ A.S := ENNReal.toReal_nonneg.trans (A.U_le 0 (0, 0))

theorem z_zero (I : ℤ × ℤ) : A.z (Fin.castSucc 0) I = fun l => A.B l I := rfl

theorem z_one (I : ℤ × ℤ) :
    A.z (Fin.castSucc 1) I = Function.update (fun l => A.B l I) A.a (A.U A.a I) := rfl

theorem z_two (I : ℤ × ℤ) :
    A.z (Fin.castSucc 2) I = Function.update (fun l => A.B l I) A.b (A.U A.b I) := rfl

theorem pattern_data (I : ℤ × ℤ) (p : Fin 3) :
    (∀ j, Measurable (A.z (Fin.castSucc p) I j)) ∧
      MemLp (A.z (Fin.castSucc p) I (A.mslot p)) 2 (A.μ I) ∧
      (eLpNorm (A.z (Fin.castSucc p) I (A.mslot p)) 2 (A.μ I)).toReal ≤
        A.S + Fintype.card A.L * A.Dc ∧
      ∀ i, A.z (Fin.castSucc p) I ((A.mslot p).succAbove i) =
        A.B ((A.mslot p).succAbove i) I := by
  have hBle := fun l => A.B_eLpNorm_le l I
  have hcard0 : 0 ≤ (Fintype.card A.L : ℝ) * A.Dc := (norm_nonneg _).trans (A.B_bound 0 I 0)
  have hS0 := A.S_nonneg
  match p with
  | 0 =>
    rw [z_zero]
    exact ⟨fun j => A.B_meas j I, A.B_memLp _ I, (hBle _).trans (by linarith), fun i => rfl⟩
  | 1 =>
    have hma : A.mslot 1 = A.a := by simp [mslot]
    rw [z_one, hma]
    refine ⟨fun j => ?_, ?_, ?_, fun i => ?_⟩
    · by_cases hj : j = A.a
      · subst hj; rw [Function.update_self]; exact A.U_meas _ _
      · rw [Function.update_of_ne hj]; exact A.B_meas j I
    · rw [Function.update_self]; exact A.U_L2 _ _
    · rw [Function.update_self]; exact (A.U_le _ _).trans (by linarith)
    · rw [Function.update_of_ne (Fin.succAbove_ne A.a i)]
  | 2 =>
    have hmb : A.mslot 2 = A.b := by simp [mslot]
    rw [z_two, hmb]
    refine ⟨fun j => ?_, ?_, ?_, fun i => ?_⟩
    · by_cases hj : j = A.b
      · subst hj; rw [Function.update_self]; exact A.U_meas _ _
      · rw [Function.update_of_ne hj]; exact A.B_meas j I
    · rw [Function.update_self]; exact A.U_L2 _ _
    · rw [Function.update_self]; exact (A.U_le _ _).trans (by linarith)
    · rw [Function.update_of_ne (Fin.succAbove_ne A.b i)]

/-- The atom triple is available at the cell: nonzero coefficients in the three slots other
than `m`. -/
def avail3 (I : ℤ × ℤ) (m : Fin 4) (v₀ v₁ v₂ : A.L) : Prop :=
  A.coef (m.succAbove 0) I v₀ ≠ 0 ∧ A.coef (m.succAbove 1) I v₁ ≠ 0 ∧
    A.coef (m.succAbove 2) I v₂ ≠ 0

open scoped Classical in
/-- Blueprint prop:base, line 1657: a pattern with at least three basic arguments is bounded by
the coefficient products times the transpose norms of the available triples. -/
theorem pattern_le {I : ℤ × ℤ} (hI : I ∈ A.cells) (p : Fin 3) :
    ‖A.Hf I (A.z (Fin.castSucc p) I)‖ ≤
      A.Dc ^ 3 * (A.S + Fintype.card A.L * A.Dc) *
        ∑ v₀, ∑ v₁, ∑ v₂, (if A.avail3 I (A.mslot p) v₀ v₁ v₂ then
          A.tnorm I (A.mslot p) v₀ v₁ v₂ else 0) := by
  have hr := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  set m := A.mslot p with hm
  set F := A.z (Fin.castSucc p) I with hF
  have hS0 := A.S_nonneg
  have hdata := A.pattern_data I p
  obtain ⟨hFm, hFL, hFle, hFs⟩ := hdata
  have h := localProgressionForm_triple_le hr hw m hFm hFL (fun i => A.coef (m.succAbove i) I)
    (fun _ => A.φ I) (fun _ v => A.φ_meas I v) (fun _ v x => A.φ_bound I v x)
    (fun i => by rw [hFs i]; rfl)
  refine h.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v₀ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v₂ _ => ?_
  have hDc : 0 ≤ A.Dc := (norm_nonneg _).trans (A.coef_le 0 I v₀)
  have htn : transposeNorm (dyadicGridLength A.G I.1) (A.w I) m
      (tripleSlots F m ![A.φ I v₀, A.φ I v₁, A.φ I v₂]) = A.tnorm I m v₀ v₁ v₂ := by
    unfold tnorm
    refine transposeNorm_congr hr hw m fun j hj x _ => ?_
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [tripleSlots_succAbove, tripleSlots_succAbove]
  rw [htn]
  have hT0 := A.tnorm_nonneg I m v₀ v₁ v₂
  by_cases hav : A.avail3 I m v₀ v₁ v₂
  · simp only [hav, ↓reduceIte]
    have h0 : ‖A.coef (m.succAbove 0) I v₀‖ * ‖A.coef (m.succAbove 1) I v₁‖ *
        ‖A.coef (m.succAbove 2) I v₂‖ ≤ A.Dc ^ 3 := by
      rw [pow_three]
      have h1 := A.coef_le (m.succAbove 0) I v₀
      have h2 := A.coef_le (m.succAbove 1) I v₁
      have h3 := A.coef_le (m.succAbove 2) I v₂
      calc _ ≤ A.Dc * A.Dc * A.Dc := by gcongr
        _ = _ := by ring
    calc _ ≤ A.Dc ^ 3 * ((A.S + Fintype.card A.L * A.Dc) * A.tnorm I m v₀ v₁ v₂) := by
          gcongr
      _ = _ := by ring
  · simp only [hav, ↓reduceIte, mul_zero]
    have hz : ‖A.coef (m.succAbove 0) I v₀‖ * ‖A.coef (m.succAbove 1) I v₁‖ *
        ‖A.coef (m.succAbove 2) I v₂‖ = 0 := by
      unfold avail3 at hav
      by_cases h1 : A.coef (m.succAbove 0) I v₀ = 0
      · rw [h1, norm_zero, zero_mul, zero_mul]
      · by_cases h2 : A.coef (m.succAbove 1) I v₁ = 0
        · rw [h2, norm_zero, mul_zero, zero_mul]
        · have h3 : A.coef (m.succAbove 2) I v₂ = 0 := by
            by_contra h3; exact hav ⟨h1, h2, h3⟩
          rw [h3, norm_zero, mul_zero]
    rw [hz, zero_mul]

end ActiveSetup

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ}

/-- A cell is active at threshold `δ` when some available atom triple has transpose norm above
`δ` (blueprint prop:base, line 1655). -/
def active (A : ActiveSetup κ c₀) (δ : ℝ) (I : ℤ × ℤ) : Prop :=
  ∃ m v₀ v₁ v₂, A.avail3 I m v₀ v₁ v₂ ∧ δ < A.tnorm I m v₀ v₁ v₂

/-- The translated path charts: near the path through `y`, the atom of label `v` is
`u ↦ Q_{y,v}(u - y)` with `Q_{y,v}` of complexity `chartTranslationBudget H`. -/
theorem exists_path_charts (A : ActiveSetup κ c₀) (hc : 1 ≤ c₀) :
    ∃ (d : ℝ → A.L → ℕ) (Q : (y : ℝ) → (v : A.L) → QuadraticChartData (d y v)),
      ∀ y v, QuadraticChartComplexity c₀ (chartTranslationBudget A.H) (Q y v) ∧
        IsBoundedQuadraticChart (Q y v) ∧ ∀ I ∈ A.cells, y ∈ dyadicGridCell A.G I.1 I.2 →
          (∃ l, A.coef l I v ≠ 0) →
          ∀ x ∈ dyadicGridCell A.G I.1 I.2, A.φ I v x = quadraticChartAtom (Q y v) (x - y) := by
  choose d B hB using A.path_chart
  have ht := fun y v => quadraticChart_translation_closure (hB y v).1 hc y
  choose Q hQ using ht
  refine ⟨d, Q, fun y v => ⟨(hQ y v).1, (hQ y v).2.1 (hB y v).2.1, fun I hI hy hl x hx => ?_⟩⟩
  rw [(hQ y v).2.2, sub_add_cancel]
  exact (hB y v).2.2 I hI hy hl x hx

theorem avail3_vec (A : ActiveSetup κ c₀) {I : ℤ × ℤ} {m : Fin 4} {v₀ v₁ v₂ : A.L}
    (h : A.avail3 I m v₀ v₁ v₂) (i : Fin 3) :
    ∃ l, A.coef l I (![v₀, v₁, v₂] i) ≠ 0 := by
  obtain ⟨h0, h1, h2⟩ := h
  fin_cases i
  · exact ⟨_, h0⟩
  · exact ⟨_, h1⟩
  · exact ⟨_, h2⟩

theorem tripleSlots_vec (A : ActiveSetup κ c₀) (I : ℤ × ℤ) (m : Fin 4) (v₀ v₁ v₂ : A.L)
    (i : Fin 3) :
    tripleSlots 0 m ![A.φ I v₀, A.φ I v₁, A.φ I v₂] (m.succAbove i) = A.φ I (![v₀, v₁, v₂] i) := by
  rw [tripleSlots_succAbove]; fin_cases i <;> rfl

open scoped Classical in
/-- Blueprint prop:base, lines 1656-1657: the inactive contributions of one available atom
triple, summed over the cells below the root, are at most `δ poly(log H, log δ⁻¹)` times the root
length (eq:triple-tail and eq:path). -/
theorem inactive_sum (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (C : ℕ) (Cr : ℝ), 0 ≤ Cr ∧ ∀ (A : ActiveSetup κ c₀) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (m : Fin 4) (v₀ v₁ v₂ : A.L),
      ∑ I ∈ A.cells, dyadicGridLength A.G I.1 *
          (if A.avail3 I m v₀ v₁ v₂ ∧ A.tnorm I m v₀ v₁ v₂ ≤ δ then A.tnorm I m v₀ v₁ v₂
            else 0) ≤
        dyadicGridLength A.G A.R.1 *
          (δ * Cr * (Real.log (chartTranslationBudget A.H) + Real.log δ⁻¹ + 1) ^ C) := by
  obtain ⟨C, Cr, hCr, htail⟩ := cells_tripleTail κ c₀ hc
  refine ⟨C, Cr, hCr, ?_⟩
  intro A δ hδ hδ1 m v₀ v₁ v₂
  obtain ⟨d, Q, hQ⟩ := A.exists_path_charts hc
  obtain ⟨cells', hcells'⟩ : ∃ c : Finset (ℤ × ℤ), c = A.cells.filter fun I => A.avail3 I m v₀ v₁
      v₂ :=
    ⟨_, rfl⟩
  have hmem' : ∀ I ∈ cells', I ∈ A.cells ∧ A.avail3 I m v₀ v₁ v₂ := fun I hI => by
    rw [hcells'] at hI; exact Finset.mem_filter.mp hI
  have hsub' : ∀ I ∈ cells', dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 :=
    fun I hI => A.sub I (hmem' I hI).1
  have hrw : ∑ I ∈ A.cells, dyadicGridLength A.G I.1 *
      (if A.avail3 I m v₀ v₁ v₂ ∧ A.tnorm I m v₀ v₁ v₂ ≤ δ then A.tnorm I m v₀ v₁ v₂ else 0) =
      ∑ I ∈ cells', dyadicGridLength A.G I.1 *
        (if A.tnorm I m v₀ v₁ v₂ ≤ δ then A.tnorm I m v₀ v₁ v₂ else 0) := by
    rw [hcells', Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hav : A.avail3 I m v₀ v₁ v₂ <;> simp [hav]
  rw [hrw]
  refine cells_sum_le_of_path A.G A.R cells' hsub' (fun I => by
    split_ifs <;> [exact A.tnorm_nonneg I m v₀ v₁ v₂; exact le_rfl]) fun y => ?_
  have h := htail (d := fun i => d y (![v₀, v₁, v₂] i)) A.G cells' A.w
    (fun I hI => A.adm I (hmem' I hI).1)
    (chartTranslationBudget A.H) δ y (fun i => Q y (![v₀, v₁, v₂] i)) (fun i => (hQ y _).1)
    (fun i => (hQ y _).2.1) hδ hδ1 m (fun I => tripleSlots 0 m ![A.φ I v₀, A.φ I v₁, A.φ I v₂])
    (fun I hI hy i x hx => by
      rw [A.tripleSlots_vec]
      exact (hQ y _).2.2 I (hmem' I hI).1 hy (A.avail3_vec (hmem' I hI).2 i) x hx)
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun I _ => ?_
  unfold tnorm
  by_cases hy : y ∈ dyadicGridCell A.G I.1 I.2 <;>
    by_cases ht : transposeNorm (dyadicGridLength A.G I.1) (A.w I) m
      (tripleSlots 0 m ![A.φ I v₀, A.φ I v₁, A.φ I v₂]) ≤ δ <;> simp [hy, ht]

open scoped Classical in
/-- Blueprint prop:base, line 1655: the active collection has path multiplicity at most
`4 |L|³ poly(log H, log δ⁻¹)`. -/
theorem active_count (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (A : ActiveSetup κ c₀) (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ y : ℝ,
      ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active δ I).card : ℝ) ≤
        4 * Fintype.card A.L ^ 3 * (C * (216 * Real.log (chartTranslationBudget A.H) +
          Real.log (sliceConst κ) + 2 * Real.log δ⁻¹) ^ C) := by
  obtain ⟨C, hC, hcnt⟩ := cells_tripleCount κ c₀ hc
  refine ⟨C, hC, ?_⟩
  intro A δ hδ hδ1 y
  obtain ⟨d, Q, hQ⟩ := A.exists_path_charts hc
  set E : Fin 4 × A.L × A.L × A.L → Finset (ℤ × ℤ) := fun t =>
    (A.cells.filter fun I => A.avail3 I t.1 t.2.1 t.2.2.1 t.2.2.2).filter fun I =>
      y ∈ dyadicGridCell A.G I.1 I.2 ∧ δ < A.tnorm I t.1 t.2.1 t.2.2.1 t.2.2.2 with hE
  have hsub : (A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active δ I) ⊆
      Finset.univ.biUnion E := by
    intro I hI
    obtain ⟨hIc, hy, hact⟩ := Finset.mem_filter.mp hI
    obtain ⟨m, v₀, v₁, v₂, hav, hlt⟩ := hact
    exact Finset.mem_biUnion.mpr ⟨(m, v₀, v₁, v₂), Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIc, hav⟩, hy, hlt⟩⟩
  have hEb : ∀ t, ((E t).card : ℝ) ≤ C * (216 * Real.log (chartTranslationBudget A.H) +
      Real.log (sliceConst κ) + 2 * Real.log δ⁻¹) ^ C := by
    rintro ⟨m, v₀, v₁, v₂⟩
    exact hcnt (d := fun i => d y (![v₀, v₁, v₂] i)) A.G
      (A.cells.filter fun I => A.avail3 I m v₀ v₁ v₂) A.w
      (fun I hI => A.adm I (Finset.mem_filter.mp hI).1)
      (chartTranslationBudget A.H) δ y (fun i => Q y (![v₀, v₁, v₂] i)) (fun i => (hQ y _).1)
      (fun i => (hQ y _).2.1) hδ hδ1 m
      (fun I => tripleSlots 0 m ![A.φ I v₀, A.φ I v₁, A.φ I v₂])
      (fun I hI hy i x hx => by
        rw [A.tripleSlots_vec]
        exact (hQ y _).2.2 I (Finset.mem_filter.mp hI).1 hy
          (A.avail3_vec (Finset.mem_filter.mp hI).2 i) x hx)
  calc _ ≤ ((Finset.univ.biUnion E).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ t, ((E t).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _t : Fin 4 × A.L × A.L × A.L, (C : ℝ) * (216 * Real.log (chartTranslationBudget A.H) +
          Real.log (sliceConst κ) + 2 * Real.log δ⁻¹) ^ C := Finset.sum_le_sum fun t _ => hEb t
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

open scoped Classical in
/-- Blueprint prop:base, proof lines 1655-1660 (active cells, eq:min-subadd): the length-weighted
sum of `|H_I(Y)|` is at most the active minima of the three patterns with at least three basic
arguments, plus the two-`U` term, plus the inactive error `δ poly(log H, log δ⁻¹) |R|` times the
coefficient and size bounds and the triple count. -/
theorem reduction (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (C : ℕ) (Cr : ℝ), 0 ≤ Cr ∧ ∀ (A : ActiveSetup κ c₀) (δ : ℝ), 0 < δ → δ ≤ 1 →
      0 ≤ A.η →
      ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.Y I)‖ ≤
        ∑ p : Fin 3, ∑ I ∈ A.cells with A.active δ I,
            dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ +
          ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.z 3 I)‖ +
          3 * Fintype.card A.L ^ 3 * (A.Dc ^ 3 * (A.S + Fintype.card A.L * A.Dc)) *
            (dyadicGridLength A.G A.R.1 *
              (δ * Cr * (Real.log (chartTranslationBudget A.H) + Real.log δ⁻¹ + 1) ^ C)) := by
  obtain ⟨C, Cr, hCr, hin⟩ := inactive_sum κ c₀ hc
  refine ⟨C, Cr, hCr, ?_⟩
  intro A δ hδ hδ1 hη
  set K := A.Dc ^ 3 * (A.S + Fintype.card A.L * A.Dc) with hK
  have hK0 : 0 ≤ K := by
    have := A.S_nonneg; have := A.Dc_nonneg; rw [hK]; positivity
  set ite3 : ℤ × ℤ → Fin 3 → A.L → A.L → A.L → ℝ := fun I p v₀ v₁ v₂ =>
    if A.avail3 I (A.mslot p) v₀ v₁ v₂ ∧ A.tnorm I (A.mslot p) v₀ v₁ v₂ ≤ δ then
      A.tnorm I (A.mslot p) v₀ v₁ v₂ else 0 with hite3
  have hite0 : ∀ I p v₀ v₁ v₂, 0 ≤ ite3 I p v₀ v₁ v₂ := fun I p v₀ v₁ v₂ => by
    simp only [hite3]; split_ifs
    · exact A.tnorm_nonneg _ _ _ _ _
    · exact le_rfl
  -- the per-cell bound
  have hcell : ∀ I ∈ A.cells, ‖A.Hf I (A.Y I)‖ ≤
      (if A.active δ I then ∑ p : Fin 3, min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ else 0) +
        ‖A.Hf I (A.z 3 I)‖ + K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ite3 I p v₀ v₁ v₂ := by
    intro I hI
    have hsplit : ‖A.Hf I (A.Y I)‖ ≤
        ∑ p : Fin 3, ‖A.Hf I (A.z (Fin.castSucc p) I)‖ + ‖A.Hf I (A.z 3 I)‖ := by
      rw [A.H_Y_eq hI, Fin.sum_univ_castSucc]
      refine (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
    have hE0 : 0 ≤ K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ite3 I p v₀ v₁ v₂ :=
      mul_nonneg hK0 (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun v₀ _ =>
        Finset.sum_nonneg fun v₁ _ => Finset.sum_nonneg fun v₂ _ => hite0 _ _ _ _ _)
    by_cases hact : A.active δ I
    · simp only [hact, ↓reduceIte]
      have hsm := A.small I hI
      have h1 : ‖A.Hf I (A.Y I)‖ ≤ min A.η
          (∑ p : Fin 3, ‖A.Hf I (A.z (Fin.castSucc p) I)‖ + ‖A.Hf I (A.z 3 I)‖) :=
        le_min hsm hsplit
      have h2 : min A.η (∑ p : Fin 3, ‖A.Hf I (A.z (Fin.castSucc p) I)‖ + ‖A.Hf I (A.z 3 I)‖) ≤
          min A.η (∑ p : Fin 3, ‖A.Hf I (A.z (Fin.castSucc p) I)‖) + ‖A.Hf I (A.z 3 I)‖ := by
        rcases le_total A.η (∑ p : Fin 3, ‖A.Hf I (A.z (Fin.castSucc p) I)‖) with h | h
        · rw [min_eq_left h]
          exact (min_le_left _ _).trans (le_add_of_nonneg_right (norm_nonneg _))
        · rw [min_eq_right h]; exact min_le_right _ _
      have h3 := min_sum_le Finset.univ (fun p : Fin 3 => ‖A.Hf I (A.z (Fin.castSucc p) I)‖)
        (fun p _ => norm_nonneg _) hη
      linarith only [hE0, h1, h2, h3]
    · simp only [hact, ↓reduceIte, zero_add]
      have hall : ∀ m v₀ v₁ v₂, A.avail3 I m v₀ v₁ v₂ → A.tnorm I m v₀ v₁ v₂ ≤ δ := by
        intro m v₀ v₁ v₂ hav; by_contra h; exact hact ⟨m, v₀, v₁, v₂, hav, not_le.mp h⟩
      have hpat : ∑ p : Fin 3, ‖A.Hf I (A.z (Fin.castSucc p) I)‖ ≤
          K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ite3 I p v₀ v₁ v₂ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun p _ => (A.pattern_le hI p).trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun v₀ _ => Finset.sum_congr rfl fun v₁ _ =>
          Finset.sum_congr rfl fun v₂ _ => ?_
        by_cases hav : A.avail3 I (A.mslot p) v₀ v₁ v₂
        · simp only [hite3, hav, hall _ v₀ v₁ v₂ hav, and_self, ↓reduceIte]
        · simp only [hite3, hav, false_and, ↓reduceIte]
      linarith
  -- summing over the cells
  have hsum : ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.Y I)‖ ≤
      ∑ I ∈ A.cells, dyadicGridLength A.G I.1 *
        ((if A.active δ I then ∑ p : Fin 3, min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ else 0) +
          ‖A.Hf I (A.z 3 I)‖ + K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ite3 I p v₀ v₁ v₂) :=
    Finset.sum_le_sum fun I hI =>
      mul_le_mul_of_nonneg_left (hcell I hI) (dyadicGridLength_pos A.G I.1).le
  have hmid : ∑ I ∈ A.cells, dyadicGridLength A.G I.1 *
        ((if A.active δ I then ∑ p : Fin 3, min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ else 0) +
          ‖A.Hf I (A.z 3 I)‖ + K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ite3 I p v₀ v₁ v₂) =
      ∑ p : Fin 3, ∑ I ∈ A.cells with A.active δ I,
          dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ +
        ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.z 3 I)‖ +
        K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ∑ I ∈ A.cells,
          dyadicGridLength A.G I.1 * ite3 I p v₀ v₁ v₂ := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · congr 1
      have hf : ∀ p : Fin 3, (∑ I ∈ A.cells with A.active δ I,
          dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖) =
          ∑ I ∈ A.cells, if A.active δ I then
            dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ else 0 :=
        fun p => Finset.sum_filter _ _
      simp only [hf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs <;> simp [Finset.mul_sum]
    · rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v₀ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v₂ _ => ?_
      refine Finset.sum_congr rfl fun I _ => ?_
      ring
  rw [hmid] at hsum
  refine hsum.trans ?_
  refine add_le_add le_rfl ?_
  · set P := dyadicGridLength A.G A.R.1 *
      (δ * Cr * (Real.log (chartTranslationBudget A.H) + Real.log δ⁻¹ + 1) ^ C) with hP
    have hb : ∀ p : Fin 3, ∀ v₀ v₁ v₂ : A.L,
        ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ite3 I p v₀ v₁ v₂ ≤ P := fun p v₀ v₁ v₂ =>
      hin A δ hδ hδ1 (A.mslot p) v₀ v₁ v₂
    calc K * ∑ p : Fin 3, ∑ v₀, ∑ v₁, ∑ v₂, ∑ I ∈ A.cells,
          dyadicGridLength A.G I.1 * ite3 I p v₀ v₁ v₂ ≤
        K * ∑ _p : Fin 3, ∑ _v₀ : A.L, ∑ _v₁ : A.L, ∑ _v₂ : A.L, P := by
          gcongr with p _ v₀ _ v₁ _ v₂ _
          exact hb p v₀ v₁ v₂
      _ = 3 * Fintype.card A.L ^ 3 * K * P := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

end ActiveSetup

/-! ### Path charts of labelled cell functions -/

/-- Charts of labelled cell functions that are nested along the tree (blueprint prop:base, line
1645, and sec:localization, line 1677: each available label is one fixed bounded quadratic chart
atom, and the functions of a label agree on nested cells where it is available). In particular,
along every path each available label is one chart atom (`PathCharts.path`). -/
def PathCharts (G : RealDyadicGrid) (cells : Finset (ℤ × ℤ)) {Λ : Type*}
    (φ : ℤ × ℤ → Λ → ℝ → ℂ) (av : ℤ × ℤ → Λ → Prop) (c₀ : ℕ) (H : ℝ) : Prop :=
  (∀ I ∈ cells, ∀ v, av I v → ∃ (d : ℕ) (B : QuadraticChartData d),
      QuadraticChartComplexity c₀ H B ∧ IsBoundedQuadraticChart B ∧ φ I v = quadraticChartAtom B) ∧
    ∀ I ∈ cells, ∀ I' ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 →
      ∀ v, av I v → av I' v → φ I v = φ I' v

/-- Path charts from charts at the available cells that agree along nested available cells. -/
theorem PathCharts.of_nested {G : RealDyadicGrid} {cells : Finset (ℤ × ℤ)} {Λ : Type*}
    {φ : ℤ × ℤ → Λ → ℝ → ℂ} {av : ℤ × ℤ → Λ → Prop} {c₀ : ℕ} {H : ℝ}
    (hchart : ∀ I ∈ cells, ∀ v, av I v → ∃ (d : ℕ) (B : QuadraticChartData d),
      QuadraticChartComplexity c₀ H B ∧ IsBoundedQuadraticChart B ∧ φ I v = quadraticChartAtom B)
    (hcons : ∀ I ∈ cells, ∀ I' ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 →
      ∀ v, av I v → av I' v → φ I v = φ I' v) :
    PathCharts G cells φ av c₀ H :=
  ⟨hchart, hcons⟩

/-- Along every path, each available label is one fixed bounded quadratic chart atom on the cells
through the path (blueprint prop:base, line 1645: "after recentering at this fixed `y`, all
unscaled oscillation parameters are fixed along the path"). -/
theorem PathCharts.path {G : RealDyadicGrid} {cells : Finset (ℤ × ℤ)} {Λ : Type*}
    {φ : ℤ × ℤ → Λ → ℝ → ℂ} {av : ℤ × ℤ → Λ → Prop} {c₀ : ℕ} {H : ℝ}
    (h : PathCharts G cells φ av c₀ H)
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀ H B ∧
      IsBoundedQuadraticChart B) :
    ∀ y v, ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀ H B ∧
      IsBoundedQuadraticChart B ∧ ∀ I ∈ cells, y ∈ dyadicGridCell G I.1 I.2 → av I v →
        ∀ x ∈ dyadicGridCell G I.1 I.2, φ I v x = quadraticChartAtom B x := by
  classical
  obtain ⟨hchart, hcons⟩ := h
  intro y v
  by_cases h : ∃ I₀ ∈ cells, y ∈ dyadicGridCell G I₀.1 I₀.2 ∧ av I₀ v
  · obtain ⟨I₀, hI₀, hy₀, hav₀⟩ := h
    obtain ⟨d, B, hBc, hBb, hBe⟩ := hchart I₀ hI₀ v hav₀
    refine ⟨d, B, hBc, hBb, fun I hI hy hav x _ => ?_⟩
    have hnd : ¬ Disjoint (dyadicGridCell G I.1 I.2) (dyadicGridCell G I₀.1 I₀.2) :=
      Set.not_disjoint_iff.mpr ⟨y, hy, hy₀⟩
    rcases le_total I.1 I₀.1 with hle | hle
    · rcases dyadicGridCell_nested_or_disjoint_of_le G hle I.2 I₀.2 with hd | hs
      · exact absurd hd hnd
      · rw [← hcons I₀ hI₀ I hI hs v hav₀ hav, hBe]
    · rcases dyadicGridCell_nested_or_disjoint_of_le G hle I₀.2 I.2 with hd | hs
      · exact absurd hd.symm hnd
      · rw [hcons I hI I₀ hI₀ hs v hav hav₀, hBe]
  · obtain ⟨d, B, hBc, hBb⟩ := hdef
    refine ⟨d, B, hBc, hBb, fun I hI hy hav => ?_⟩
    exact absurd ⟨I, hI, hy, hav⟩ h

theorem PathCharts.mono_c {G : RealDyadicGrid} {cells : Finset (ℤ × ℤ)} {Λ : Type*}
    {φ : ℤ × ℤ → Λ → ℝ → ℂ} {av : ℤ × ℤ → Λ → Prop} {c₀ c₁ : ℕ} {H : ℝ}
    (h : PathCharts G cells φ av c₀ H) (hc : c₀ ≤ c₁) : PathCharts G cells φ av c₁ H := by
  refine ⟨fun I hI v hv => ?_, h.2⟩
  obtain ⟨d, B, hBc, hBb, hB⟩ := h.1 I hI v hv
  exact ⟨d, B, quadraticChartComplexity_order_mono hBc hc, hBb, hB⟩

theorem PathCharts.mono {G : RealDyadicGrid} {cells : Finset (ℤ × ℤ)} {Λ : Type*}
    {φ : ℤ × ℤ → Λ → ℝ → ℂ} {av av' : ℤ × ℤ → Λ → Prop} {c₀ : ℕ} {H H' : ℝ}
    (h : PathCharts G cells φ av c₀ H) (hav : ∀ I v, av' I v → av I v) (hH : H ≤ H') :
    PathCharts G cells φ av' c₀ H' := by
  refine ⟨fun I hI v hv => ?_, fun I hI I' hI' hII' v hv hv' =>
    h.2 I hI I' hI' hII' v (hav I v hv) (hav I' v hv')⟩
  obtain ⟨d, B, hBc, hBb, hB⟩ := h.1 I hI v (hav I v hv)
  exact ⟨d, B, quadraticChartComplexity_mono hBc hH, hBb, hB⟩

/-- Path charts of two label families combine. -/
theorem PathCharts.sum {G : RealDyadicGrid} {cells : Finset (ℤ × ℤ)} {Λ₁ Λ₂ : Type*}
    {φ₁ : ℤ × ℤ → Λ₁ → ℝ → ℂ} {φ₂ : ℤ × ℤ → Λ₂ → ℝ → ℂ} {av₁ : ℤ × ℤ → Λ₁ → Prop}
    {av₂ : ℤ × ℤ → Λ₂ → Prop} {c₀ : ℕ} {H : ℝ} (h₁ : PathCharts G cells φ₁ av₁ c₀ H)
    (h₂ : PathCharts G cells φ₂ av₂ c₀ H) :
    PathCharts G cells (fun I => Sum.elim (φ₁ I) (φ₂ I)) (fun I => Sum.elim (av₁ I) (av₂ I))
      c₀ H := by
  refine ⟨fun I hI v hv => ?_, fun I hI I' hI' hII' v hv hv' => ?_⟩
  · cases v with
    | inl v => exact h₁.1 I hI v hv
    | inr v => exact h₂.1 I hI v hv
  · cases v with
    | inl v => exact h₁.2 I hI I' hI' hII' v hv hv'
    | inr v => exact h₂.2 I hI I' hI' hII' v hv hv'

/-- The low lists have path charts: births are canonical along paths. -/
theorem LowList.pathCharts {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ : ℕ}
    {H : ℝ} (X : LowList G J N R c₀ H) (cells : Finset (ℤ × ℤ)) :
    PathCharts G cells (fun I l => X.atom I l) (fun I l => X.coef I l ≠ 0) c₀ H := by
  refine PathCharts.of_nested (fun I _ l _ => ⟨_, _, X.complexity _ l, X.bounded _ l, rfl⟩)
    fun I hI I' hI' hII' l hl hl' => ?_
  unfold LowList.atom
  rw [X.birth_eq_of_le (X.coef_avail I l hl) (X.coef_avail I' l hl') hII']

namespace AccSetup
variable {S : AccSetup}

/-- The accurate-fit atoms are detection charts. -/
theorem Hyp.atoms_good (h : S.Hyp) (d : ℕ) (c : ℤ × ℤ) :
    ∀ i < (fitState S.G S.M S.P S.O d c).2, ∃ p : Σ d, QuadraticChartData d,
      QuadraticChartComplexity S.c₂ S.B p.2 ∧ IsBoundedQuadraticChart p.2 ∧
        (fitState S.G S.M S.P S.O d c).1 i = quadraticChartAtom p.2 := by
  refine fitState_inv S.G S.M S.P S.O (fun φ => ∃ p : Σ d, QuadraticChartData d,
      QuadraticChartComplexity S.c₂ S.B p.2 ∧ IsBoundedQuadraticChart p.2 ∧
        φ = quadraticChartAtom p.2) ?_ d c
  intro c a n _ hP
  simp only [P, not_or, not_not] at hP
  obtain ⟨hc, hns⟩ := hP
  obtain ⟨p, hgood, hO⟩ := fitOracleAtom_good
    (h.detect c a n hc (h.res_measurable c a n)
      (h.res_eLpNorm_le hc (kernelHull_of_not_formSmall (coarse_tree h hc) hns) a n) hns)
  exact ⟨p, hgood.1, hgood.2.1, hO⟩

/-- The scalars of the accurate-fit system have path charts, given path charts of the predictor
system. -/
theorem Hyp.system_pathCharts (h : S.Hyp) (K : ℤ × ℤ) (cells : Finset (ℤ × ℤ)) {c₀ : ℕ} {H : ℝ}
    (hP₀ : PathCharts S.G cells (fun c v => S.P₀.scalarAt c v) (fun c v => v ∈ S.P₀.avail c) c₀ H)
    (hc₀ : S.c₂ ≤ c₀) (hBH : S.B ≤ H) :
    PathCharts S.G cells (fun c v => (S.system K).scalarAt c v)
      (fun c v => v ∈ (S.system K).avail c) c₀ H := by
  classical
  have hfit : PathCharts S.G cells (fun c (m : Fin S.M) => S.fatoms K c m)
      (fun c m => (m : ℕ) < S.fcount K c) c₀ H := by
    refine PathCharts.of_nested (fun c hc m hm => ?_) fun c hc c' hc' hcc' m hm hm' => ?_
    · unfold fcount at hm
      split_ifs at hm with hcond
      · obtain ⟨p, h1, h2, h3⟩ := h.atoms_good _ _ m hm
        refine ⟨p.1, p.2, ?_, h2, h3⟩
        exact quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h1 hBH) hc₀
      · omega
    · unfold fcount at hm hm'
      split_ifs at hm hm' with hcond hcond'
      · exact (fit_prefix hcc' hcond'.2.2).2 m hm'
      all_goals omega
  have hsum := hP₀.sum hfit
  refine ⟨fun c hc v hv => ?_, fun c hc c' hc' hcc' v hv hv' => ?_⟩
  · cases v with
    | inl v =>
      obtain ⟨d, B, hBc, hBb, hB⟩ := hsum.1 c hc (Sum.inl v) (by simpa [system] using hv)
      exact ⟨d, B, hBc, hBb, by simpa [system, sc] using hB⟩
    | inr m =>
      obtain ⟨d, B, hBc, hBb, hB⟩ := hsum.1 c hc (Sum.inr m) (by
        simpa [system, fitLabels] using hv)
      exact ⟨d, B, hBc, hBb, by simpa [system, sc] using hB⟩
  · cases v with
    | inl v =>
      have := hsum.2 c hc c' hc' hcc' (Sum.inl v) (by simpa [system] using hv)
        (by simpa [system] using hv')
      simpa [system, sc] using this
    | inr m =>
      have := hsum.2 c hc c' hc' hcc' (Sum.inr m) (by simpa [system, fitLabels] using hv)
        (by simpa [system, fitLabels] using hv')
      simpa [system, sc] using this

end AccSetup

section PredSystemCharts
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ c₁ : ℕ}
  {H : ℝ} (Xi Xk : LowList G J N R c₀ H) (a i k b : Fin 4) (B D : ℝ)
  (pkg : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b B D c₁)

/-- The predictor system has path charts: its scalars are conjugate predictor charts, fixed along
paths by the canonical births of the low labels. -/
theorem predSystem_pathCharts {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (cells : Finset (ℤ × ℤ))
    (hcells : ∀ I ∈ cells, I ∈ dyadicFiniteTree G J N) :
    PathCharts G cells (fun c v => (predSystem κ Xi Xk a i k b B D pkg hε0 hε1).scalarAt c v)
      (fun c v => v ∈ (predSystem κ Xi Xk a i k b B D pkg hε0 hε1).avail c) c₁ D := by
  classical
  refine PathCharts.of_nested (fun c hc v hv => ?_) fun c hc c' hc' hcc' v hv hv' => ?_
  · have hPA : PredAvail κ Xi Xk a i k b B D pkg c v := by simpa [predSystem] using hv
    set! P := pkg (Xi.birth c v.1) (Xk.birth c v.2.1) v.1 v.2.1
    have hlt : (v.2.2 : ℕ) < P.L.card := hPA.2.2.2
    set! ℓ := (P.L.equivFin.symm ⟨v.2.2, hlt⟩).1
    have hℓ : ℓ ∈ P.L := (P.L.equivFin.symm ⟨v.2.2, hlt⟩).2
    obtain ⟨hb1, -, hc1, -⟩ := P.bdd ℓ hℓ
    refine ⟨_, conjugateQuadraticChart (P.ψa ℓ), conjugateQuadraticChart_complexity hc1,
      conjugateQuadraticChart_bounded hb1, ?_⟩
    funext y
    change predScalar κ Xi Xk a i k b B D pkg c v y = _
    unfold predScalar predScalarB
    simp only [hPA, ↓reduceIte]
    rw [conjugateQuadraticChart_atom]
    split_ifs with h2
    · rfl
    · exact absurd hlt h2
  · have hPA' : PredAvail κ Xi Xk a i k b B D pkg c' v := by simpa [predSystem] using hv'
    exact predScalar_eq κ Xi Xk a i k b B D pkg (hcells c hc) hcc' hPA'

end PredSystemCharts

namespace PathColumnSystem
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {V : Type} [Fintype V]
  (P : PathColumnSystem G J N V)

/-! ### Coefficients of the current projections of a path-uniform system -/

theorem colData (c : ℤ × ℤ) : ColData (P.scalarAt c) P.weight := fun v =>
  ⟨P.scalar_meas c v, P.scalar_bound c v, (P.weight_pos v).le, P.weight_le v⟩

theorem colOK (c : ℤ × ℤ) (v : V) :
    ColOK (dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight v :=
  (P.colData c).ok (dyadicGridCell_measurable _ _ _)
    (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top) v

/-- The cell projection of the system is the column-range projection of its available labels. -/
theorem range_eq_colRange (c : ℤ × ℤ) :
    P.range c = colRange (dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight (P.avail c) := by
  unfold range colRange
  congr 1
  refine Set.image_congr fun v _ => ?_
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (P.column_memLp c v), col_coeFn (P.colOK c v)] with y h1 h2
  rw [column, h1, h2]

/-- The coefficients of the current projection at a cell (zero off the available labels). -/
noncomputable def coef (c : ℤ × ℤ) (z : ColumnL2 V) (v : V) : ℂ := by
  classical
  exact if v ∈ P.avail c then
    colCoeff (dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight (P.avail c) z v else 0

/-- The physical part of the cell projection is the combination of the scalars with the
coefficients. -/
theorem proj_none_ae (c : ℤ × ℤ) (z : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∈ dyadicGridCell G c.1 c.2 →
      (P.proj c z : ℝ → ColumnHilbert V) y none = ∑ v, P.coef c z v * P.scalarAt c v y := by
  classical
  have hp : P.proj c = (colRange (dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight
      (P.avail c)).starProjection := by
    unfold proj; ext x : 1; exact starProjection_congr (P.range_eq_colRange c) x
  filter_upwards [colProj_none (s := dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight
    (P.avail c) z] with y hy hyc
  rw [hp, hy hyc, colPhys]
  rw [← Finset.sum_subset (Finset.subset_univ (P.avail c)) fun v _ hv => by
    simp [coef, hv]]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [P.colOK c v, ↓reduceIte, coef, hv]

/-- Private-coordinate recovery: the coefficients are bounded by the inverse square root of the
private weight times the normalized `L²` norm of the input on the cell. -/
theorem coef_sq_le (c : ℤ × ℤ) (z : ColumnL2 V) (v : V) :
    ‖P.coef c z v‖ ^ 2 * P.weight v * dyadicGridLength G c.1 ≤
      ∫ y in dyadicGridCell G c.1 c.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  classical
  unfold coef
  split_ifs with hv
  · have h := colCoeff_recovery (s := dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight
      (P.avail c) z hv (P.colOK c v)
    rw [measureReal_def, dyadicGridCell_volume,
      ENNReal.toReal_ofReal (dyadicGridLength_pos G c.1).le] at h
    refine h.trans ?_
    have h2 := colRange_energy_le (dyadicGridCell_measurable G c.1 c.2) (P.scalarAt c) P.weight
      (P.avail c) z
    calc _ ≤ ‖(colRange (dyadicGridCell G c.1 c.2) (P.scalarAt c) P.weight
          (P.avail c)).starProjection z‖ ^ 2 := by
          rw [columnInput_norm_sq_integral]
          exact setIntegral_le_integral ((Lp.memLp _).integrable_norm_pow two_ne_zero)
            (Filter.Eventually.of_forall fun _ => by positivity)
      _ ≤ _ := h2
  · simp only [norm_zero]
    have := (P.weight_pos v).le
    have : 0 ≤ ∫ y in dyadicGridCell G c.1 c.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    simpa using this

end PathColumnSystem

/-! ### Basic projections (blueprint prop:base, lines 1611-1613; line 1859) -/

open scoped Classical in
/-- The physical part `(P_{u(I)} Z)_phys` of the current projection of an augmented input, with
`u(I)` the tree cell above `I` (zero outside the tree). -/
noncomputable def ColumnDepthFamily.currentZ {V : Type*} [Fintype V] (Ψ : ColumnDepthFamily V)
    (Z : ColumnL2 V) (I : ℤ × ℤ) (y : ℝ) : ℂ :=
  if h : Ψ.anc I ∈ Ψ.D.cells then
    (cellColumnProjection Ψ.D Ψ.A h Z : ℝ → ColumnHilbert V) y none
  else 0

/-- A basic projection below the root `R`: an inherited column depth family on the grid of `R`
whose root contains `R`, and an augmented input `Z` of energy at most `CF |R|` on `R`; its value
at a cell `I` is the physical part of the current projection `(P_I Z)_phys` (blueprint prop:base,
line 1611: "each `B_l` is a difference of at most two current basic projections"). -/
structure BasicProjection (G : RealDyadicGrid) (R : ℤ × ℤ) (CF : ℝ) where
  /-- Finite label type of the basic column projection system. -/
  V : Type
  [fin : Fintype V]
  /-- Depth-indexed column family defining the basic projections. -/
  Ψ : ColumnDepthFamily V
  /-- Column L² input whose projections generate the basic components. -/
  Z : ColumnL2 V
  grid : Ψ.D.grid = G
  root_sub : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G Ψ.D.root.1 Ψ.D.root.2
  energy : ∫ y in dyadicGridCell G R.1 R.2, ‖(Z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
    CF * dyadicGridLength G R.1

attribute [instance] BasicProjection.fin

namespace BasicProjection
variable {G : RealDyadicGrid} {R : ℤ × ℤ} {CF : ℝ}

/-- The value of a basic projection at a cell. -/
noncomputable def val (P : BasicProjection G R CF) (I : ℤ × ℤ) (y : ℝ) : ℂ :=
  P.Ψ.currentZ P.Z I y

/-- The zero input on the family of another basic projection. -/
noncomputable def zero (P : BasicProjection G R CF) (hCF : 0 ≤ CF) : BasicProjection G R CF where
  V := P.V
  Ψ := P.Ψ
  Z := 0
  grid := P.grid
  root_sub := P.root_sub
  energy := by
    have : ∫ y in dyadicGridCell G R.1 R.2, ‖((0 : ColumnL2 P.V) : ℝ → ColumnHilbert P.V) y‖ ^ 2
        = 0 := by
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
      simp
    rw [this]
    exact mul_nonneg hCF (dyadicGridLength_pos G R.1).le

theorem zero_val (P : BasicProjection G R CF) (hCF : 0 ≤ CF) (I : ℤ × ℤ) :
    ∀ᵐ y ∂volume, (P.zero hCF).val I y = 0 := by
  classical
  unfold val ColumnDepthFamily.currentZ
  change ∀ᵐ y ∂volume, (if h : P.Ψ.anc I ∈ P.Ψ.D.cells then
    (cellColumnProjection P.Ψ.D P.Ψ.A h 0 : ℝ → ColumnHilbert P.V) y none else 0) = 0
  split_ifs with h
  · rw [map_zero]
    filter_upwards [Lp.coeFn_zero (ColumnHilbert P.V) 2 (volume : Measure ℝ)] with y hy
    rw [hy]; rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- A column budget `X` bounds the inverse private weights of a basic projection by `X²`
(eq:columnbudget, `budget⁻¹ ≤ √ε_v`). -/
theorem inv_privateWeight_le (P : BasicProjection G R CF) {X : ℝ} (hX : P.Ψ.D.budget ≤ X)
    (v : P.V) : (P.Ψ.D.privateWeight v)⁻¹ ≤ X ^ 2 := by
  have hb := P.Ψ.D.two_le_budget
  have hw := P.Ψ.D.privateWeight_pos v
  have hl := P.Ψ.D.private_lower v
  have h1 : (P.Ψ.D.budget⁻¹) ^ 2 ≤ P.Ψ.D.privateWeight v := by
    have := pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) hl 2
    rwa [Real.sq_sqrt hw.le] at this
  have h2 : (P.Ψ.D.privateWeight v)⁻¹ ≤ ((P.Ψ.D.budget⁻¹) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos (inv_pos.mpr (by linarith)) 2) h1
  rw [inv_pow, inv_inv] at h2
  exact h2.trans (pow_le_pow_left₀ (by linarith) hX 2)

/-- The cells of `S` are decision cells of the family of a basic projection, not deeper than its
leaf depth, and the columns available there are bounded quadratic chart atoms of order `c₀` and
complexity at most `H` on those cells (blueprint prop:base, line 1607: the complexities of the
basic data; line 1676: the tags of the original basic columns). -/
def HasChartsOn (P : BasicProjection G R CF) (S : Set (ℤ × ℤ)) (c₀ : ℕ) (H : ℝ) : Prop :=
  ∀ c ∈ S, c ∈ P.Ψ.D.cells ∧ c.1 ≤ P.Ψ.N ∧
    ∀ v ∈ P.Ψ.A.labels c, ∃ (d : ℕ) (Φ : QuadraticChartData d),
    QuadraticChartComplexity c₀ H Φ ∧ IsBoundedQuadraticChart Φ ∧
    ∀ y ∈ dyadicGridCell G c.1 c.2, P.Ψ.D.scalar v y = quadraticChartAtom Φ y

theorem HasChartsOn.mono {P : BasicProjection G R CF} {S S' : Set (ℤ × ℤ)} {c₀ c₀' : ℕ}
    {H H' : ℝ} (h : P.HasChartsOn S c₀ H) (hS : S' ⊆ S) (hc : c₀ ≤ c₀') (hH : H ≤ H') :
    P.HasChartsOn S' c₀' H' := fun c hcS => by
  obtain ⟨m1, m2, hch⟩ := h c (hS hcS)
  refine ⟨m1, m2, fun v hv => ?_⟩
  obtain ⟨d, Φ, h1, h2, h3⟩ := hch v hv
  exact ⟨d, Φ, quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h1 hH) hc, h2,
    h3⟩

/-- The input of a basic projection has energy at most `CF |c|` on every cell `c` of `S`
(blueprint prop:base, lines 1607-1608: the basic inputs keep bounded normalized `L²` sizes on the
cells, the original inputs being normalized on every cell of the tree). -/
def CellEnergyOn (P : BasicProjection G R CF) (S : Set (ℤ × ℤ)) : Prop :=
  ∀ c ∈ S, ∫ y in dyadicGridCell G c.1 c.2, ‖(P.Z : ℝ → ColumnHilbert P.V) y‖ ^ 2 ≤
    CF * dyadicGridLength G c.1

theorem CellEnergyOn.mono {P : BasicProjection G R CF} {S S' : Set (ℤ × ℤ)}
    (h : P.CellEnergyOn S) (hS : S' ⊆ S) : P.CellEnergyOn S' := fun c hc => h c (hS hc)

theorem zero_cellEnergyOn (P : BasicProjection G R CF) (hCF : 0 ≤ CF) (S : Set (ℤ × ℤ)) :
    (P.zero hCF).CellEnergyOn S := fun c _ => by
  have : ∫ y in dyadicGridCell G c.1 c.2, ‖((0 : ColumnL2 P.V) : ℝ → ColumnHilbert P.V) y‖ ^ 2
      = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp
  change ∫ y in dyadicGridCell G c.1 c.2, ‖((0 : ColumnL2 P.V) : ℝ → ColumnHilbert P.V) y‖ ^ 2 ≤
    _
  rw [this]
  exact mul_nonneg hCF (dyadicGridLength_pos G c.1).le

end BasicProjection

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)

/-- The column budget of an active setup, `2 + |L| (1 + D_c)`, from its label count and
coefficient bound. The basic projections of its column representation have column budgets at most
this (blueprint prop:base, line 1607: counts, complexities and inverse private weights are
`exp(k^{O(1)})`); a column budget `X` bounds the inverse private weights by `X²`
(`BasicProjection.inv_privateWeight_le`). -/
noncomputable def colBudget : ℝ := 2 + Fintype.card A.L * (1 + A.Dc)

/-- The column representation of the basic arguments of an active setup (blueprint prop:base,
lines 1607 and 1611-1613): on every cell of the setup each basic argument `B_l` is, almost
everywhere on the cell, the difference of two current basic projections below the root, with
inputs of energy at most `CF |R|` on the root and at most `CF |I|` on every cell `I` of the setup,
column budgets at most `A.colBudget`, and columns that are charts of order `c₀` and complexity at
most `A.H` on the cells of the setup. -/
def HasColumnRep (CF : ℝ) : Prop :=
  ∀ l : Fin 4, ∃ P₁ P₂ : BasicProjection A.G A.R CF, P₁.Ψ.D.budget ≤ A.colBudget ∧
    P₂.Ψ.D.budget ≤ A.colBudget ∧ P₁.HasChartsOn ↑A.cells c₀ A.H ∧
    P₂.HasChartsOn ↑A.cells c₀ A.H ∧ P₁.CellEnergyOn ↑A.cells ∧ P₂.CellEnergyOn ↑A.cells ∧
    ∀ I ∈ A.cells,
    ∀ᵐ y ∂volume, y ∈ dyadicGridCell A.G I.1 I.2 → A.B l I y = P₁.val I y - P₂.val I y

/-- The column representation below a sub-root `R'`: on every cell of the setup below `R'` each
basic argument is the difference of two current basic projections below `R'` with column budgets
at most `A.colBudget` and columns that are charts of order `c₀` and complexity at most `A.H` on
those cells (blueprint prop:normalized, lines 2840-2842: restarts keep the basic arguments). -/
def ColumnRepBelow (R' : ℤ × ℤ) (CF : ℝ) : Prop :=
  ∀ l : Fin 4, ∃ P₁ P₂ : BasicProjection A.G R' CF, P₁.Ψ.D.budget ≤ A.colBudget ∧
    P₂.Ψ.D.budget ≤ A.colBudget ∧
    P₁.HasChartsOn {I | I ∈ A.cells ∧ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2}
      c₀ A.H ∧
    P₂.HasChartsOn {I | I ∈ A.cells ∧ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2}
      c₀ A.H ∧
    P₁.CellEnergyOn {I | I ∈ A.cells ∧ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2} ∧
    P₂.CellEnergyOn {I | I ∈ A.cells ∧ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2} ∧
    ∀ I ∈ A.cells,
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2 →
    ∀ᵐ y ∂volume, y ∈ dyadicGridCell A.G I.1 I.2 → A.B l I y = P₁.val I y - P₂.val I y

theorem hasColumnRep_of_below {CF : ℝ} (h : A.ColumnRepBelow A.R CF) : A.HasColumnRep CF :=
  fun l => by
    obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := h l
    exact ⟨P₁, P₂, h₁, h₂, c₁.mono (fun I hI => ⟨hI, A.sub I hI⟩) le_rfl le_rfl,
      c₂.mono (fun I hI => ⟨hI, A.sub I hI⟩) le_rfl le_rfl,
      e₁.mono (fun I hI => ⟨hI, A.sub I hI⟩), e₂.mono (fun I hI => ⟨hI, A.sub I hI⟩),
      fun I hI => hP I hI (A.sub I hI)⟩

open Classical in
/-- The sub-root properties of an active setup (blueprint prop:base, lines 1611-1622, asserted on
every normalized restart root): below every dyadic sub-root `R'` of the root, the basic-side
energies are at most `E |R'|`, the two-`U` term is at most `η₀ E |R'|`, and the basic arguments
have a column representation below `R'`. -/
def SubRootProps (η₀ E : ℝ) : Prop :=
  ∀ R' : ℤ × ℤ, dyadicGridCell A.G R'.1 R'.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 →
    (∀ l, ∑ I ∈ A.cells with dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2,
      dyadicGridLength A.G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
        E * dyadicGridLength A.G R'.1) ∧
    ∑ I ∈ A.cells with dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R'.1 R'.2,
      dyadicGridLength A.G I.1 * ‖A.Hf I (A.z 3 I)‖ ≤ η₀ * (E * dyadicGridLength A.G R'.1) ∧
    A.ColumnRepBelow R' 1

theorem SubRootProps.mono {A : ActiveSetup κ c₀} {η₀ E E' : ℝ} (h : A.SubRootProps η₀ E)
    (hη₀ : 0 ≤ η₀) (hE : E ≤ E') :
    A.SubRootProps η₀ E' := fun R' hR' => by
  obtain ⟨h1, h2, h3⟩ := h R' hR'
  have hr := (dyadicGridLength_pos A.G R'.1).le
  exact ⟨fun l => (h1 l).trans (mul_le_mul_of_nonneg_right hE hr),
    h2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE hr) hη₀), h3⟩

end ActiveSetup

namespace PathColumnSystem
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {V : Type} [Fintype V]
  (P : PathColumnSystem G J N V)

/-- On a tree cell below `R` the current projection of the system rooted at `R` is the cell
projection of the system. -/
theorem family_currentZ_ae {R I : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N)
    (hI : I ∈ dyadicFiniteTree G J N)
    (hIR : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2) (z : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 →
      (P.family R hR).currentZ z I y = ∑ v, P.coef I z v * P.scalarAt I v y := by
  classical
  have hIN : I.1 ≤ (P.family R hR).N := by
    have := ((dyadicFiniteTree_mem_iff G J I N).mp hI).2
    change I.1 ≤ J.1 + N; omega
  have hanc : (P.family R hR).anc I = I := (P.family R hR).anc_self hIN
  have hmem : I ∈ (P.rooted R).cells := (below_mem_iff hR I).mpr ⟨hI, hIR⟩
  have hmem' : (P.family R hR).anc I ∈ (P.family R hR).D.cells := by rw [hanc]; exact hmem
  have key : ∀ (c : ℤ × ℤ) (hc : c ∈ (P.family R hR).D.cells), c = I →
      cellColumnProjection (P.family R hR).D (P.family R hR).A hc z =
        cellColumnProjection (P.rooted R) (P.mask R hR) hmem z := by
    rintro c hc rfl; rfl
  have e : (P.family R hR).currentZ z I = fun y =>
      (cellColumnProjection (P.rooted R) (P.mask R hR) hmem z : ℝ → ColumnHilbert V) y none := by
    funext y
    unfold ColumnDepthFamily.currentZ
    simp only [hmem', ↓reduceDIte]
    rw [key _ hmem' hanc]
  rw [e, P.rooted_proj hR hmem]
  exact P.proj_none_ae I z

/-- The current projections of the system rooted at `R` applied to an input of energy at most
`CF |R|` on `R`, as a basic projection. -/
noncomputable def basicProjection {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (z : ColumnL2 V)
    {CF : ℝ} (hz : ∫ y in dyadicGridCell G R.1 R.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
      CF * dyadicGridLength G R.1) : BasicProjection G R CF where
  V := V
  Ψ := P.family R hR
  Z := z
  grid := rfl
  root_sub := subset_rfl
  energy := hz

theorem basicProjection_val_ae {R I : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N)
    (hI : I ∈ dyadicFiniteTree G J N)
    (hIR : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2) (z : ColumnL2 V) {CF : ℝ}
    (hz : ∫ y in dyadicGridCell G R.1 R.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤
      CF * dyadicGridLength G R.1) :
    ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 →
      (P.basicProjection hR z hz).val I y = ∑ v, P.coef I z v * P.scalarAt I v y :=
  P.family_currentZ_ae hR hI hIR z

end PathColumnSystem

/-- The budget of a path-uniform system with private weights at least `ε`. -/
theorem PathColumnSystem.budget_le {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {V : Type}
    [Fintype V] (P : PathColumnSystem G J N V) {ε : ℝ} (hε : 0 < ε) (hw : ∀ v, ε ≤ P.weight v) :
    P.budget ≤ 2 + Fintype.card V + Fintype.card V * (Real.sqrt ε)⁻¹ := by
  unfold PathColumnSystem.budget
  have : ∑ v, (Real.sqrt (P.weight v))⁻¹ ≤ ∑ _v : V, (Real.sqrt ε)⁻¹ :=
    Finset.sum_le_sum fun v _ => inv_anti₀ (Real.sqrt_pos.mpr hε) (Real.sqrt_le_sqrt (hw v))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  linarith

section BaseActive
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {Wa Wb : Type} [Fintype Wa] [Fintype Wb]
  (Pa : PathColumnSystem G J N Wa) (Pb : PathColumnSystem G J N Wb)
  (Za : ColumnL2 Wa) (Zb : ColumnL2 Wb) {Ga Gb : Type} [Fintype Ga] [Fintype Gb]
  (cga : ℤ × ℤ → Ga → ℂ) (aga : ℤ × ℤ → Ga → ℝ → ℂ)
  (cgb : ℤ × ℤ → Gb → ℂ) (agb : ℤ × ℤ → Gb → ℝ → ℂ) (i k a b : Fin 4)

/-! ### The active setup of the base data -/

/-- The labels of the base data: the two low lists, and for each high slot the labels of its
system and of its previous fit. -/
abbrev BaseLabel : Type := Xi.Λ ⊕ Xk.Λ ⊕ (Wa ⊕ Ga) ⊕ (Wb ⊕ Gb)

open scoped Classical in
/-- The coefficients of the basic arguments. -/
noncomputable def baseCoef (l : Fin 4) (I : ℤ × ℤ) : BaseLabel Xi Xk (Wa := Wa) (Wb := Wb)
    (Ga := Ga) (Gb := Gb) → ℂ
  | .inl li => if l = i then Xi.coef I li else 0
  | .inr (.inl lk) => if l = k then Xk.coef I lk else 0
  | .inr (.inr (.inl (.inl v))) => if l = a then Pa.coef I Za v else 0
  | .inr (.inr (.inl (.inr m))) => if l = a then -cga I m else 0
  | .inr (.inr (.inr (.inl v))) => if l = b then Pb.coef I Zb v else 0
  | .inr (.inr (.inr (.inr m))) => if l = b then -cgb I m else 0

/-- The atoms of the basic arguments. -/
noncomputable def baseAtom (I : ℤ × ℤ) : BaseLabel Xi Xk (Wa := Wa) (Wb := Wb) (Ga := Ga)
    (Gb := Gb) → ℝ → ℂ
  | .inl li => Xi.atom I li
  | .inr (.inl lk) => Xk.atom I lk
  | .inr (.inr (.inl (.inl v))) => Pa.scalarAt I v
  | .inr (.inr (.inl (.inr m))) => aga I m
  | .inr (.inr (.inr (.inl v))) => Pb.scalarAt I v
  | .inr (.inr (.inr (.inr m))) => agb I m

theorem baseB_i (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (I : ℤ × ℤ) (y : ℝ) :
    ∑ v, baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b i I v * baseAtom Xi Xk Pa Pb aga agb I v y =
      Xi.val I y := by
  simp only [Fintype.sum_sum_type, baseCoef, baseAtom, hik, hia, hib, ↓reduceIte, zero_mul,
    Finset.sum_const_zero, add_zero, LowList.val]

theorem baseB_k (hik : i ≠ k) (hka : k ≠ a) (hkb : k ≠ b) (I : ℤ × ℤ) (y : ℝ) :
    ∑ v, baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b k I v * baseAtom Xi Xk Pa Pb aga agb I v y =
      Xk.val I y := by
  simp only [Fintype.sum_sum_type, baseCoef, baseAtom, hik.symm, hka, hkb, ↓reduceIte, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, LowList.val]

theorem baseB_a (hia : i ≠ a) (hka : k ≠ a) (hab : a ≠ b) (I : ℤ × ℤ) (y : ℝ) :
    ∑ v, baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b a I v * baseAtom Xi Xk Pa Pb aga agb I v y =
      ∑ v, Pa.coef I Za v * Pa.scalarAt I v y - ∑ m, cga I m * aga I m y := by
  simp only [Fintype.sum_sum_type, baseCoef, baseAtom, hia.symm, hka.symm, hab, ↓reduceIte,
    zero_mul, Finset.sum_const_zero, zero_add, add_zero, neg_mul, Finset.sum_neg_distrib]
  ring

theorem baseB_b (hib : i ≠ b) (hkb : k ≠ b) (hab : a ≠ b) (I : ℤ × ℤ) (y : ℝ) :
    ∑ v, baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b b I v * baseAtom Xi Xk Pa Pb aga agb I v y =
      ∑ v, Pb.coef I Zb v * Pb.scalarAt I v y - ∑ m, cgb I m * agb I m y := by
  simp only [Fintype.sum_sum_type, baseCoef, baseAtom, hib.symm, hkb.symm, hab.symm, ↓reduceIte,
    zero_mul, Finset.sum_const_zero, zero_add, add_zero, neg_mul, Finset.sum_neg_distrib]
  ring

omit [Fintype Ga] [Fintype Gb] in
/-- A nonzero base coefficient of a label means availability in its family. -/
theorem base_av {I : ℤ × ℤ} {v : BaseLabel Xi Xk (Wa := Wa) (Wb := Wb) (Ga := Ga) (Gb := Gb)}
    (h : ∃ l, baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b l I v ≠ 0) :
    match v with
    | .inl li => Xi.coef I li ≠ 0
    | .inr (.inl lk) => Xk.coef I lk ≠ 0
    | .inr (.inr (.inl (.inl w))) => w ∈ Pa.avail I
    | .inr (.inr (.inl (.inr m))) => cga I m ≠ 0
    | .inr (.inr (.inr (.inl w))) => w ∈ Pb.avail I
    | .inr (.inr (.inr (.inr m))) => cgb I m ≠ 0 := by
  classical
  have hcoefP : ∀ (W : Type) [Fintype W] (P : PathColumnSystem G J N W) (Z : ColumnL2 W) I w,
      P.coef I Z w ≠ 0 → w ∈ P.avail I := fun W _ P Z I w h => by
    by_contra hw; exact h (by simp [PathColumnSystem.coef, hw])
  obtain ⟨l, hl⟩ := h
  rcases v with li | lk | (w | m) | (w | m) <;> simp only [baseCoef] at hl <;> split_ifs at hl
  all_goals first
    | exact absurd rfl hl
    | exact hl
    | exact hcoefP _ Pa Za I w hl
    | exact hcoefP _ Pb Zb I w hl
    | exact fun h0 => hl (by rw [h0, neg_zero])

omit [Fintype Ga] [Fintype Gb] in
/-- Nested charts of the base labels from those of the four families. -/
theorem base_pathCharts (cells : Finset (ℤ × ℤ)) {c₀' : ℕ} {H' : ℝ}
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H') :
    PathCharts G cells (baseAtom Xi Xk Pa Pb aga agb)
      (fun I v => ∃ l, baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b l I v ≠ 0) c₀' H' := by
  refine ⟨fun I hI v hv => ?_, fun I hI I' hI' hII' v hv hv' => ?_⟩
  · have h := base_av Xi Xk Pa Pb Za Zb cga cgb i k a b hv
    rcases v with li | lk | (w | m) | (w | m)
    · exact hXi.1 I hI li h
    · exact hXk.1 I hI lk h
    · exact hPa.1 I hI w h
    · exact hga.1 I hI m h
    · exact hPb.1 I hI w h
    · exact hgb.1 I hI m h
  · have h := base_av Xi Xk Pa Pb Za Zb cga cgb i k a b hv
    have h' := base_av Xi Xk Pa Pb Za Zb cga cgb i k a b hv'
    rcases v with li | lk | (w | m) | (w | m)
    · exact hXi.2 I hI I' hI' hII' li h h'
    · exact hXk.2 I hI I' hI' hII' lk h h'
    · exact hPa.2 I hI I' hI' hII' w h h'
    · exact hga.2 I hI I' hI' hII' m h h'
    · exact hPb.2 I hI I' hI' hII' w h h'
    · exact hgb.2 I hI I' hI' hII' m h h'

end BaseActive

section BaseActiveSetup
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {Wa Wb : Type} [Fintype Wa] [Fintype Wb]
  (Pa : PathColumnSystem G J N Wa) (Pb : PathColumnSystem G J N Wb)
  (Za : ColumnL2 Wa) (Zb : ColumnL2 Wb) {Ga Gb : Type} [Fintype Ga] [Fintype Gb]
  (cga : ℤ × ℤ → Ga → ℂ) (aga : ℤ × ℤ → Ga → ℝ → ℂ)
  (cgb : ℤ × ℤ → Gb → ℂ) (agb : ℤ × ℤ → Gb → ℝ → ℂ) {i k a b : Fin 4}

/-- The basic argument in a high slot: the current projection of the high system minus the
previous fit. -/
noncomputable def baseHighB (I : ℤ × ℤ) (y : ℝ) : ℂ :=
  ∑ v, Pa.coef I Za v * Pa.scalarAt I v y - ∑ m, cga I m * aga I m y

/-- The active setup of the base data on the cells of a root (blueprint prop:base, eq:Y and
lines 1641-1660): basic arguments from the low lists and the current high projections minus the
previous fits, basic sides `U_e = Y_e - B_e`. -/
noncomputable def baseActiveSetup {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η) :
    ActiveSetup κ c₀' where
  G := G
  R := R
  cells := cells
  sub := hsub
  w := w
  adm := hw
  L := BaseLabel Xi Xk (Wa := Wa) (Wb := Wb) (Ga := Ga) (Gb := Gb)
  φ := baseAtom Xi Xk Pa Pb aga agb
  φ_meas := fun I v => by
    rcases v with li | lk | (v | m) | (v | m)
    · exact Xi.atom_measurable I li
    · exact Xk.atom_measurable I lk
    · exact Pa.scalar_meas I v
    · exact hagm I m
    · exact Pb.scalar_meas I v
    · exact hbgm I m
  φ_bound := fun I v x => by
    rcases v with li | lk | (v | m) | (v | m)
    · exact Xi.atom_bound I li x
    · exact Xk.atom_bound I lk x
    · exact Pa.scalar_bound I v x
    · exact hagb I m x
    · exact Pb.scalar_bound I v x
    · exact hbgb I m x
  H := H'
  coef := fun l I v => by
    classical
    exact if I ∈ cells then baseCoef Xi Xk Pa Pb Za Zb cga cgb i k a b l I v else 0
  path_chart := fun y v => by
    classical
    obtain ⟨d, B, h1, h2, h3⟩ := (base_pathCharts Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b cells
      hXi hXk hPa hPb hga hgb).path hdef y v
    refine ⟨d, B, h1, h2, fun I hI hy ⟨l, hl⟩ => h3 I hI hy ⟨l, ?_⟩⟩
    simpa only [hI, ↓reduceIte] using hl
  nested_chart := fun I hI v hv => by
    classical
    obtain ⟨l, hl⟩ := hv
    exact (base_pathCharts Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b cells
      hXi hXk hPa hPb hga hgb).1 I hI v ⟨l, by simpa only [hI, ↓reduceIte] using hl⟩
  nested_cons := fun I hI I' hI' hII' v hv hv' => by
    classical
    obtain ⟨l, hl⟩ := hv
    obtain ⟨l', hl'⟩ := hv'
    exact (base_pathCharts Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b cells
      hXi hXk hPa hPb hga hgb).2 I hI I' hI' hII' v ⟨l, by simpa only [hI, ↓reduceIte] using hl⟩
        ⟨l', by simpa only [hI', ↓reduceIte] using hl'⟩
  Dc := Dc
  Dc_nonneg := by linarith
  coef_le := fun l I v => by
    classical
    split_ifs with hI
    swap
    · simp only [norm_zero]; linarith
    rcases v with li | lk | (v | m) | (v | m) <;> simp only [baseCoef] <;> split_ifs <;>
      first
      | simp only [norm_zero]; linarith
      | exact (Xi.coef_le I li).trans hDc
      | exact (Xk.coef_le I lk).trans hDc
      | exact hPac I hI v
      | exact hPbc I hI v
      | (rw [norm_neg]; exact (hcga I m).trans hDc)
      | (rw [norm_neg]; exact (hcgb I m).trans hDc)
  a := a
  b := b
  hab := hab
  U := fun l I => if l = a then Ya I - baseHighB Pa Za cga aga I
    else if l = b then Yb I - baseHighB Pb Zb cgb agb I else 0
  U_meas := fun l I => by
    have hBa : Measurable (baseHighB Pa Za cga aga I) :=
      (Finset.measurable_sum _ fun v _ => measurable_const.mul (Pa.scalar_meas I v)).sub
        (Finset.measurable_sum _ fun m _ => measurable_const.mul (hagm I m))
    have hBb : Measurable (baseHighB Pb Zb cgb agb I) :=
      (Finset.measurable_sum _ fun v _ => measurable_const.mul (Pb.scalar_meas I v)).sub
        (Finset.measurable_sum _ fun m _ => measurable_const.mul (hbgm I m))
    split_ifs
    · exact (hYam I).sub hBa
    · exact (hYbm I).sub hBb
    · exact measurable_const
  S := S
  U_L2 := fun l I => by
    split_ifs
    · exact hUa I
    · exact hUb I
    · exact MemLp.zero
  U_le := fun l I => by
    split_ifs
    · exact hUa' I
    · exact hUb' I
    · simpa using hS
  η := η
  small := fun I hI => by
    classical
    refine le_of_eq_of_le ?_ (hsmall I hI)
    simp only [hI, ↓reduceIte]
    congr 2
    funext l
    rcases fin_four_cover hia.symm hka.symm hab hik hib hkb l with h | h | h | h <;> rw [h]
    · simp only [hab, or_false, ↓reduceIte, slots4_a]
      funext y
      simp only [Pi.add_apply, baseB_a Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hia hka hab,
        baseHighB, Pi.sub_apply]
      ring
    · simp only [hia, hib, or_self, ↓reduceIte, slots4_i hia.symm, add_zero]
      funext y
      exact baseB_i Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hia hib I y
    · simp only [hka, hkb, or_self, ↓reduceIte, slots4_k hka.symm hik, add_zero]
      funext y
      exact baseB_k Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hka hkb I y
    · simp only [hab.symm, or_true, ↓reduceIte]
      have : slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I) b = Yb I := by
        simp [slots4, hab.symm, hib.symm, hkb.symm]
      rw [this]
      funext y
      simp only [Pi.add_apply, baseB_b Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hib hkb hab,
        baseHighB, Pi.sub_apply]
      ring

end BaseActiveSetup

namespace PathColumnSystem
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {V : Type} [Fintype V]
  (P : PathColumnSystem G J N V)

/-! ### Current projections and basic sides of a path-uniform system -/

theorem mem_partition_self {R I : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N)
    (hIR : I ∈ pathBelow G J N R) : I ∈ ((P.family R hR).partition I.1).cells := by
  have hI := (below_mem_iff hR I).mp hIR
  refine ((P.family R hR).mem_partition I.1 I).mpr ⟨?_, hI.2⟩
  have h1 : R.1 ≤ I.1 := dyadicGridCell_depth_le_of_subset G I R hI.2
  have h2 : I.1 ≤ J.1 + N := ((dyadicFiniteTree_mem_iff G J I N).mp hI.1).2
  exact ((P.family R hR).depth_eq h1 h2).symm

/-- The physical part of the current projection of a rooted family on a cell is the combination
of the cell scalars with the cell coefficients. -/
theorem cur_ae {R I : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (hIR : I ∈ pathBelow G J N R)
    (z : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 →
      ((P.family R hR).proj I.1 z : ℝ → ColumnHilbert V) y none =
        ∑ v, P.coef I z v * P.scalarAt I v y := by
  have h1 := P.family_proj_ae hR I.1 (P.mem_partition_self hR hIR) z
  rw [Filter.EventuallyEq, ae_restrict_iff' (dyadicGridCell_measurable _ _ _)] at h1
  filter_upwards [h1, P.proj_none_ae I z] with y hy1 hy2 hyI
  rw [hy1 hyI, hy2 hyI]

theorem cur_measurable (I : ℤ × ℤ) (z : ColumnL2 V) :
    Measurable fun y => ∑ v, P.coef I z v * P.scalarAt I v y :=
  Finset.measurable_sum _ fun v _ => measurable_const.mul (P.scalar_meas I v)

/-- Local contraction of the current projection. -/
theorem cur_sq_le {R I : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (hIR : I ∈ pathBelow G J N R)
    (z : ColumnL2 V) :
    ∫ y in dyadicGridCell G I.1 I.2, ‖∑ v, P.coef I z v * P.scalarAt I v y‖ ^ 2 ≤
      ∫ y in dyadicGridCell G I.1 I.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  have hI := (below_mem_iff hR I).mp hIR
  set Ψ := P.family R hR
  have hcon := Ψ.setIntegral_proj_le I.1 z (I := I) hI.2 (by
    rw [((P.family R hR).mem_partition I.1 I).mp (P.mem_partition_self hR hIR) |>.1.symm])
  refine le_trans (integral_mono_ae ?_ (integrableOn_norm_sq_Lp _ _) ?_) hcon
  · have := cell_isFiniteMeasure G I.1 I.2
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖∑ v, P.coef I z v * P.scalarAt I v y‖ ≤ C :=
      ⟨∑ v, ‖P.coef I z v‖, fun y => (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (P.scalar_bound I v y))⟩
    exact Integrable.of_bound (C := C ^ 2)
      ((P.cur_measurable I z).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2)
  · rw [Filter.EventuallyLE, ae_restrict_iff' (dyadicGridCell_measurable _ _ _)]
    filter_upwards [P.cur_ae hR hIR z] with y hy hyI
    rw [← hy hyI]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_coord_le _ _) 2

/-- The rolling increments `(P_{s+K₀} - P_s) F` on cells below a root have square energy at
most `K₀²` times the input energy on the root (blueprint prop:base, eq:basic-side). -/
theorem rolling_cells {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (z : ColumnL2 V) (K₀ : ℕ)
    (T : Finset (ℤ × ℤ)) (hT : ∀ I ∈ T, I ∈ pathBelow G J N R) :
    ∑ I ∈ T, ∫ y in dyadicGridCell G I.1 I.2,
      ‖((P.family R hR).proj (I.1 + K₀) z : ℝ → ColumnHilbert V) y none -
        ∑ v, P.coef I z v * P.scalarAt I v y‖ ^ 2 ≤
      (K₀ : ℝ) ^ 2 * ∫ y in dyadicGridCell G R.1 R.2, ‖(z : ℝ → ColumnHilbert V) y‖ ^ 2 := by
  have hr := (P.family R hR).rolling_energy z K₀ T fun I hI => ((below_mem_iff hR I).mp (hT I
    hI)).2
  refine le_trans (Finset.sum_le_sum fun I hI => ?_) hr
  refine integral_mono_ae ?_ (((Lp.memLp _).sub (Lp.memLp _)).integrable_norm_pow
    two_ne_zero).integrableOn ?_
  · exact (((ColumnDepthFamily.memLp_coord_restrict ((P.family R hR).proj (I.1 + K₀) z) _).sub
      (ColumnDepthFamily.memLp_coord_restrict ((P.family R hR).proj I.1 z) _)).integrable_norm_pow
      two_ne_zero).congr (by
        rw [Filter.EventuallyEq, ae_restrict_iff' (dyadicGridCell_measurable _ _ _)]
        filter_upwards [P.cur_ae hR (hT I hI) z] with y hy hyI
        simp only [Pi.sub_apply]
        rw [hy hyI])
  · rw [Filter.EventuallyLE, ae_restrict_iff' (dyadicGridCell_measurable _ _ _)]
    filter_upwards [P.cur_ae hR (hT I hI) z] with y hy hyI
    rw [← hy hyI]
    have := norm_coord_le (((P.family R hR).proj (I.1 + K₀) z : ℝ → ColumnHilbert V) y -
      ((P.family R hR).proj I.1 z : ℝ → ColumnHilbert V) y) none
    rw [PiLp.sub_apply] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2

end PathColumnSystem

theorem eLpNorm_normalized_toReal_sq {a r : ℝ} (hr : 0 < r) {g : ℝ → ℂ}
    (hm : MemLp g 2 (normalizedIntervalMeasure a r)) :
    (eLpNorm g 2 (normalizedIntervalMeasure a r)).toReal ^ 2 =
      r⁻¹ * ∫ y in Set.Ico a (a + r), ‖g y‖ ^ 2 := by
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have heq : ∫ y, ‖g y‖ ^ (2 : ENNReal).toReal ∂normalizedIntervalMeasure a r =
      r⁻¹ * ∫ y in Set.Ico a (a + r), ‖g y‖ ^ 2 := by
    rw [normalizedIntervalMeasure, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le), smul_eq_mul,
      setIntegral_congr_set Ico_ae_eq_Icc.symm]
    congr 2; funext y; simp
  rw [heq]
  have hX0 : 0 ≤ r⁻¹ * ∫ y in Set.Ico a (a + r), ‖g y‖ ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => by positivity)
  have e : (2 : ENNReal).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [e, ← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt hX0]

namespace AccSetup
variable {S : AccSetup}

/-- The current physical projection of the attempt system rooted at `K` on a cell. -/
noncomputable def cur (S : AccSetup) (K I : ℤ × ℤ) (y : ℝ) : ℂ :=
  ∑ v, (S.system K).coef I S.Z v * (S.system K).scalarAt I v y

/-- The final fine projections of a coarse cell are the delayed projections of the attempt
system rooted at its segment. -/
theorem Hyp.phys_st_ae (h : S.Hyp) {K R I : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree S.G S.J S.N)
    (hIc : I ∈ dyadicFiniteTree S.G S.J S.Nc) (hseg : S.tree.seg I = K)
    (hIR : S.cell I ⊆ S.cell R) :
    ∀ᵐ y ∂volume, y ∈ S.cell I →
      S.phys I (S.tree.st I).1 (S.tree.st I).2 y =
        (((S.system K).family R hR).proj (I.1 + S.K₀) S.Z : ℝ → ColumnHilbert S.W) y none := by
  have hth := h.treeHyp
  obtain ⟨-, hIK, -, -⟩ := hth.seg_spec hIc
  rw [hseg] at hIK
  have hKI := dyadicGridCell_depth_le_of_subset S.G I K hIK
  have hIT := coarse_tree h hIc
  have hst : S.tree.st I = ((fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).1,
      (fitState S.G S.M S.P S.O (I.1 - K.1).toNat I).2) := by
    change S.tree.state (S.tree.depthIn I) I = _
    unfold GreedyTree.depthIn GreedyTree.state
    rw [hseg]
    rfl
  have hdel := h.system_delayed_ae hR ((PathColumnSystem.below_mem_iff hR I).mpr ⟨hIT, hIR⟩)
    hIc hIK hKI
  filter_upwards [hdel] with y hy hyI
  rw [hst, ← hy hyI]
  rfl

theorem cur_measurable (S : AccSetup) (K I : ℤ × ℤ) : Measurable (S.cur K I) :=
  (S.system K).cur_measurable I S.Z

theorem cur_bound (S : AccSetup) (K I : ℤ × ℤ) : ∃ C, ∀ y, ‖S.cur K I y‖ ≤ C :=
  ⟨∑ v, ‖(S.system K).coef I S.Z v‖, fun y => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun v _ => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((S.system K).scalar_bound I v y))⟩

theorem integrableOn_sq_of_bound {s : Set ℝ} (hs : volume s < ⊤) {g : ℝ → ℂ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    IntegrableOn (fun y => ‖g y‖ ^ 2) s := by
  have : IsFiniteMeasure (volume.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
  exact Integrable.of_bound (C := C ^ 2) (hg.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2)

/-- Blueprint prop:base, eq:basic-side: the basic sides `U_{e,I} = (P_{s+K₀} - P_s) F_e` on the
coarse cells of one segment below a common root `R` have square energy at most `K₀² |R|`. -/
theorem Hyp.basicSide (h : S.Hyp) {K R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree S.G S.J S.N)
    (hRT : kernelHull S.G S.J S.N S.w R) (T : Finset (ℤ × ℤ))
    (hT : ∀ I ∈ T, I ∈ dyadicFiniteTree S.G S.J S.Nc ∧
      S.tree.seg I = K ∧ S.cell I ⊆ S.cell R) :
    ∑ I ∈ T, ∫ y in S.cell I, ‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y‖ ^ 2 ≤
      (S.K₀ : ℝ) ^ 2 * dyadicGridLength S.G R.1 := by
  have hroll := (S.system K).rolling_cells hR S.Z S.K₀ T fun I hI =>
    (PathColumnSystem.below_mem_iff hR I).mpr ⟨coarse_tree h (hT I hI).1, (hT I hI).2.2⟩
  have hE := h.energy_cell_le hR hRT
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun I hI => ?_)) (hroll.trans
    (mul_le_mul_of_nonneg_left hE (by positivity)))
  refine setIntegral_congr_ae (dyadicGridCell_measurable _ _ _) ?_
  filter_upwards [h.phys_st_ae hR (hT I hI).1 (hT I hI).2.1 (hT I hI).2.2] with y hy hyI
  rw [hy hyI]
  rfl

/-- The basic side on one coarse cell has `L²(I)` energy at most `4 |I|`. -/
theorem Hyp.U_sq_le (h : S.Hyp) {K I : ℤ × ℤ} (hIc : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hIH : kernelHull S.G S.J S.N S.w I) :
    ∫ y in S.cell I, ‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y‖ ^ 2 ≤
      4 * dyadicGridLength S.G I.1 := by
  have hIT := coarse_tree h hIc
  have hv : volume (S.cell I) < ⊤ := by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top
  obtain ⟨C₁, hC₁⟩ := phys_bound (S := S) I (S.tree.st I).1 (S.tree.st I).2
  obtain ⟨C₂, hC₂⟩ := S.cur_bound K I
  have hi1 := integrableOn_sq_of_bound hv (phys_measurable _ _ _) hC₁
  have hi2 := integrableOn_sq_of_bound hv (S.cur_measurable K I) hC₂
  have h1 := h.phys_sq_le hIc hIH (S.tree.st I).1 (S.tree.st I).2
  have h2 : ∫ y in S.cell I, ‖S.cur K I y‖ ^ 2 ≤ dyadicGridLength S.G I.1 :=
    ((S.system K).cur_sq_le hIT ((PathColumnSystem.below_mem_iff hIT I).mpr ⟨hIT, le_rfl⟩)
      S.Z).trans (h.energy_cell_le hIT hIH)
  calc ∫ y in S.cell I, ‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y‖ ^ 2
      ≤ ∫ y in S.cell I, (2 * ‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y‖ ^ 2 +
          2 * ‖S.cur K I y‖ ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          ((hi1.const_mul 2).add (hi2.const_mul 2)) (Filter.Eventually.of_forall fun y => ?_)
        have h3 := norm_sub_le (S.phys I (S.tree.st I).1 (S.tree.st I).2 y) (S.cur K I y)
        have h0 := norm_nonneg (S.phys I (S.tree.st I).1 (S.tree.st I).2 y -
          S.cur K I y)
        have h4 := pow_le_pow_left₀ h0 h3 2
        nlinarith only [sq_nonneg (‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y‖ - ‖S.cur K I y‖),
            h3, h0]
    _ ≤ 4 * dyadicGridLength S.G I.1 := by
        rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
          integral_const_mul]
        linarith

/-- Coefficient bound from private-coordinate recovery: `|c_v| ≤ ε^{-1/2}`. -/
theorem Hyp.coef_le (h : S.Hyp) {K I : ℤ × ℤ} (hIT : I ∈ dyadicFiniteTree S.G S.J S.N)
    (hIH : kernelHull S.G S.J S.N S.w I) {ε : ℝ} (hε : 0 < ε) (hw : ∀ v, ε ≤ S.wt v) (v : S.W) :
    ‖(S.system K).coef I S.Z v‖ ≤ Real.sqrt ε⁻¹ := by
  have h1 := (S.system K).coef_sq_le I S.Z v
  have h2 := h.energy_cell_le hIT hIH
  have hr := dyadicGridLength_pos S.G I.1
  have hwv : ε ≤ (S.system K).weight v := hw v
  refine Real.le_sqrt_of_sq_le ?_
  suffices hs : ‖(S.system K).coef I S.Z v‖ ^ 2 * ε ≤ 1 by
    calc ‖(S.system K).coef I S.Z v‖ ^ 2 = ‖(S.system K).coef I S.Z v‖ ^ 2 * ε * ε⁻¹ := by
          field_simp
      _ ≤ 1 * ε⁻¹ := by gcongr
      _ = ε⁻¹ := one_mul _
  have h3 : ‖(S.system K).coef I S.Z v‖ ^ 2 * (S.system K).weight v ≤ 1 := by
    have := h1.trans h2
    have h4 : ‖(S.system K).coef I S.Z v‖ ^ 2 * (S.system K).weight v * dyadicGridLength S.G I.1
        ≤ 1 * dyadicGridLength S.G I.1 := by rw [one_mul]; exact this
    exact le_of_mul_le_mul_right h4 hr
  calc ‖(S.system K).coef I S.Z v‖ ^ 2 * ε ≤
      ‖(S.system K).coef I S.Z v‖ ^ 2 * (S.system K).weight v :=
        mul_le_mul_of_nonneg_left hwv (by positivity)
    _ ≤ 1 := h3

end AccSetup

/-! ### Pair smallness of the replaced tuple on one cell -/

/-- Blueprint prop:base, proof lines 1641-1642 (one cell): if every pair of the tuple
`(f_a - g_a, φ, φ', f_b - g_b)` in the slots `a, i, k, b` is `η₀`-small and the residuals
`f_e - P_e` are `δ_e`-small, then every pair of the replaced tuple `(P_a - g_a, φ, φ', P_b - g_b)`
is `η₀ + (2 + 2S)(δ_a + δ_b) + (1 + S_a) δ_b`-small. -/
theorem slots4_pairSmall {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) {q : ℝ} (hq : 2 ≤ q) {a i k b : Fin 4}
    (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b) (hkb : k ≠ b)
    {f : Fin 4 → ℝ → ℂ} (hfm : ∀ l, Measurable (f l))
    (hfq : ∀ l, eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure a₀ r) ≤ 1)
    {φ φ' ga gb Pa Pb : ℝ → ℂ} (hφ : Measurable φ) (hφ' : Measurable φ') (hga : Measurable ga)
    (hgb : Measurable gb) (hPa : Measurable Pa) (hPb : Measurable Pb) {S Sa Sb η₀ δa δb : ℝ}
    (hS : 0 < S) (hSa : 0 < Sa) (hφS : ∀ y, ‖φ y‖ ≤ S) (hφ'S : ∀ y, ‖φ' y‖ ≤ S)
    (hgaS : ∀ y, ‖ga y‖ ≤ S) (hgbS : ∀ y, ‖gb y‖ ≤ S) (hPaS : ∀ y, ‖Pa y‖ ≤ Sa)
    (hPbS : ∀ y, ‖Pb y‖ ≤ Sb) (hδa : 0 ≤ δa) (hδb : 0 ≤ δb)
    (hsa : FormSmall a₀ r w a q (f a - Pa) δa) (hsb : FormSmall a₀ r w b q (f b - Pb) δb)
    (hpairs : ∀ s s', s ≠ s' → PairSmall a₀ r w s s'
      (slots4 a i k (f a - ga) φ φ' (f b - gb) s) (slots4 a i k (f a - ga) φ φ' (f b - gb) s')
      η₀) :
    ∀ s s', s ≠ s' → PairSmall a₀ r w s s'
      (slots4 a i k (Pa - ga) φ φ' (Pb - gb) s) (slots4 a i k (Pa - ga) φ φ' (Pb - gb) s')
      (η₀ + (2 + 2 * S) * (δa + δb) + (1 + Sa) * δb) := by
  classical
  let C : YCell κ :=
    { a₀ := a₀
      r := r
      w := w
      q := q
      i := i
      j := k
      a := a
      b := b
      X := slots4 a i k (f a - ga) φ φ' (f b - gb)
      f := f
      g := fun l => if l = a then ga else gb
      Pa := Pa
      Pb := Pb
      S := S
      Sa := Sa
      Sb := Sb
      η₀ := η₀
      δa := δa
      δb := δb
      r_pos := hr
      adm := hw
      two_le_q := hq
      hij := hik
      hia := hai.symm
      hib := hib
      hja := hak.symm
      hjb := hkb
      hab := hab
      X_meas := fun l => by
        rcases fin_four_cover hai hak hab hik hib hkb l with rfl | rfl | rfl | rfl
        · rw [slots4_a]; exact (hfm _).sub hga
        · rw [slots4_i hai]; exact hφ
        · rw [slots4_k hak hik]; exact hφ'
        · rw [slots4_b hab hib hkb]; exact (hfm _).sub hgb
      low_bound := fun y => by
        rw [slots4_i hai, slots4_k hak hik]; exact ⟨hφS y, hφ'S y⟩
      f_meas := hfm
      f_norm := hfq
      g_meas := fun l => by
        split_ifs
        · exact hga
        · exact hgb
      g_bound := fun y => by
        simp only [↓reduceIte, hab.symm]; exact ⟨hgaS y, hgbS y⟩
      Xa := by simp only [slots4_a, ↓reduceIte]
      Xb := by simp only [slots4_b hab hib hkb, hab.symm, ↓reduceIte]
      Pa_meas := hPa
      Pb_meas := hPb
      Pa_bound := hPaS
      Pb_bound := hPbS
      S_pos := hS
      Sa_pos := hSa
      δa_nonneg := hδa
      δb_nonneg := hδb
      small_a := hsa
      small_b := hsb
      pairs := hpairs }
  have hY : C.Y = slots4 a i k (Pa - ga) φ φ' (Pb - gb) := by
    funext l
    simp only [YCell.Y, C]
    rcases fin_four_cover hai hak hab hik hib hkb l with rfl | rfl | rfl | rfl
    · simp only [↓reduceIte, slots4_a]
    · simp only [hai.symm, hib, ↓reduceIte, slots4_i hai]
    · simp only [hak.symm, hkb, ↓reduceIte, slots4_k hak hik]
    · simp only [hab.symm, ↓reduceIte, slots4_b hab hib hkb]
  intro s s' hss
  have := C.Y_pairSmall hss
  rw [hY] at this
  exact this

section BaseActiveSetupFacts
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {Wa Wb : Type} [Fintype Wa] [Fintype Wb]
  (Pa : PathColumnSystem G J N Wa) (Pb : PathColumnSystem G J N Wb)
  (Za : ColumnL2 Wa) (Zb : ColumnL2 Wb) {Ga Gb : Type} [Fintype Ga] [Fintype Gb]
  (cga : ℤ × ℤ → Ga → ℂ) (aga : ℤ × ℤ → Ga → ℝ → ℂ)
  (cgb : ℤ × ℤ → Gb → ℂ) (agb : ℤ × ℤ → Gb → ℝ → ℂ) {i k a b : Fin 4}

theorem baseActiveSetup_U_a {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η) (I : ℤ × ℤ) :
    (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb hab
        hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
          hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm
            S hS hUa hUb hUa' hUb' η hsmall).U a I = Ya I - baseHighB Pa Za cga aga I := by
  change (if a = a then _ else _) = _
  simp only [↓reduceIte]

theorem baseActiveSetup_U_b {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η) (I : ℤ × ℤ) :
    (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb hab
        hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
          hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm
            S hS hUa hUb hUa' hUb' η hsmall).U b I = Yb I - baseHighB Pb Zb cgb agb I := by
  change (if b = a then _ else if b = b then _ else 0) = _
  simp only [hab.symm, ↓reduceIte]

theorem baseActiveSetup_B {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η) {I : ℤ × ℤ} (hI : I ∈ cells) (l :
          Fin 4) :
    (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb hab
        hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
          hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm
            S hS hUa hUb hUa' hUb' η hsmall).B l I = fun x => ∑ v, baseCoef Xi Xk Pa Pb Za Zb cga
                cgb i k a b l I v *
      baseAtom Xi Xk Pa Pb aga agb I v x := by
  classical
  funext x
  change ∑ v, (if I ∈ cells then _ else 0) * _ = _
  simp only [hI, ↓reduceIte]
  rfl

theorem baseActiveSetup_Y {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η) {I : ℤ × ℤ} (hI : I ∈ cells) :
    (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb hab
        hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
          hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm
            S hS hUa hUb hUa' hUb' η hsmall).Y I = slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb
                I) := by
  classical
  funext l
  rw [ActiveSetup.Y, (baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik
      hia hib hka hkb hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb hdef Dc hDc hPac hPbc hcga
          hcgb Ya Yb hYam hYbm S hS hUa hUb hUa' hUb' η hsmall hI l)]
  change _ + (if l = a ∨ l = b then _ else 0) = _
  rcases fin_four_cover hia.symm hka.symm hab hik hib hkb l with h | h | h | h <;> rw [h]
  · rw [baseActiveSetup_U_a]
    simp only [true_or, ↓reduceIte, slots4_a]
    funext y
    simp only [Pi.add_apply, baseB_a Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hia hka hab,
      baseHighB, Pi.sub_apply]
    ring
  · simp only [hia, hib, or_self, ↓reduceIte, slots4_i hia.symm, add_zero]
    funext y
    exact baseB_i Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hia hib I y
  · simp only [hka, hkb, or_self, ↓reduceIte, slots4_k hka.symm hik, add_zero]
    funext y
    exact baseB_k Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hka hkb I y
  · rw [baseActiveSetup_U_b]
    simp only [or_true, ↓reduceIte, slots4_b hab hib hkb]
    funext y
    simp only [Pi.add_apply, baseB_b Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hib hkb hab,
      baseHighB, Pi.sub_apply]
    ring

theorem baseActiveSetup_z3 {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η) {I : ℤ × ℤ} (hI : I ∈ cells) :
    (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb hab
        hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
          hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm
            S hS hUa hUb hUa' hUb' η hsmall).z 3 I = slots4 a i k (Ya I - baseHighB Pa Za cga aga
                I) (Xi.val I) (Xk.val I)
      (Yb I - baseHighB Pb Zb cgb agb I) := by
  classical
  funext l
  change Function.update (Function.update (fun l => (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga
      cgb agb R cells hsub w hw hik hia hib hka hkb hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga
          hgb hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm S hS hUa hUb hUa' hUb' η
            hsmall).B l I) a
              ((baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib
                  hka hkb hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
                    hdef Dc hDc hPac hPbc hcga
                      hcgb Ya Yb hYam hYbm S hS hUa hUb hUa' hUb' η hsmall).U a I)) b
                          ((baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw
                              hik hia hib hka hkb hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga
                                  hgb hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm S hS
                                    hUa hUb hUa' hUb' η hsmall).U b I) l = _
  rw [baseActiveSetup_U_a, baseActiveSetup_U_b]
  rcases fin_four_cover hia.symm hka.symm hab hik hib hkb l with h | h | h | h <;> rw [h]
  · rw [Function.update_of_ne hab, Function.update_self, slots4_a]
  · rw [Function.update_of_ne hib, Function.update_of_ne hia, slots4_i hia.symm,
      (baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb
          hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
            hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam
              hYbm S hS hUa hUb hUa' hUb' η hsmall hI i)]
    funext y
    exact baseB_i Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hia hib I y
  · rw [Function.update_of_ne hkb, Function.update_of_ne hka, slots4_k hka.symm hik,
      (baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb
          hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
            hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam
              hYbm S hS hUa hUb hUa' hUb' η hsmall hI k)]
    funext y
    exact baseB_k Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hka hkb I y
  · rw [Function.update_self, slots4_b hab hib hkb]

/-- The column representation below a sub-root `R'` of the base active setup from the
representations of its four basic arguments below `R'` (blueprint prop:base, lines 1611-1613). -/
theorem baseActiveSetup_columnRepBelow {c₀' : ℕ} (R : ℤ × ℤ) (cells : Finset (ℤ × ℤ))
    (hsub : ∀ I ∈ cells, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ cells, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (hik : i ≠ k) (hia : i ≠ a) (hib : i ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hagm : ∀ I m, Measurable (aga I m)) (hagb : ∀ I m y, ‖aga I m y‖ ≤ 1)
    (hbgm : ∀ I m, Measurable (agb I m)) (hbgb : ∀ I m y, ‖agb I m y‖ ≤ 1)
    (H' : ℝ)
    (hXi : PathCharts G cells (fun I l => Xi.atom I l) (fun I l => Xi.coef I l ≠ 0) c₀' H')
    (hXk : PathCharts G cells (fun I l => Xk.atom I l) (fun I l => Xk.coef I l ≠ 0) c₀' H')
    (hPa : PathCharts G cells (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c₀' H')
    (hPb : PathCharts G cells (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c₀' H')
    (hga : PathCharts G cells aga (fun I m => cga I m ≠ 0) c₀' H')
    (hgb : PathCharts G cells agb (fun I m => cgb I m ≠ 0) c₀' H')
    (hdef : ∃ (d : ℕ) (B : QuadraticChartData d), QuadraticChartComplexity c₀' H' B ∧
      IsBoundedQuadraticChart B)
    (Dc : ℝ) (hDc : 1 ≤ Dc) (hPac : ∀ I ∈ cells, ∀ v, ‖Pa.coef I Za v‖ ≤ Dc)
    (hPbc : ∀ I ∈ cells, ∀ v, ‖Pb.coef I Zb v‖ ≤ Dc) (hcga : ∀ I m, ‖cga I m‖ ≤ 1)
    (hcgb : ∀ I m, ‖cgb I m‖ ≤ 1)
    (Ya Yb : ℤ × ℤ → ℝ → ℂ) (hYam : ∀ I, Measurable (Ya I)) (hYbm : ∀ I, Measurable (Yb I))
    (S : ℝ) (hS : 0 ≤ S)
    (hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za cga aga I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb cgb agb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ S)
    (η : ℝ)
    (hsmall : ∀ I ∈ cells, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ η)
    {CF X : ℝ} (R' : ℤ × ℤ)
    (hX : X ≤ 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Wa + Fintype.card Ga) +
      (Fintype.card Wb + Fintype.card Gb) : ℕ) : ℝ) * (1 + Dc))
    (hri : ∃ P₁ P₂ : BasicProjection G R' CF, P₁.Ψ.D.budget ≤ X ∧ P₂.Ψ.D.budget ≤ X ∧
      P₁.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₂.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₁.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      P₂.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      ∀ I ∈ cells,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 → ∀ᵐ y ∂volume,
      y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = P₁.val I y - P₂.val I y)
    (hrk : ∃ P₁ P₂ : BasicProjection G R' CF, P₁.Ψ.D.budget ≤ X ∧ P₂.Ψ.D.budget ≤ X ∧
      P₁.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₂.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₁.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      P₂.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      ∀ I ∈ cells,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 → ∀ᵐ y ∂volume,
      y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = P₁.val I y - P₂.val I y)
    (hra : ∃ P₁ P₂ : BasicProjection G R' CF, P₁.Ψ.D.budget ≤ X ∧ P₂.Ψ.D.budget ≤ X ∧
      P₁.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₂.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₁.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      P₂.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      ∀ I ∈ cells,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 → ∀ᵐ y ∂volume,
      y ∈ dyadicGridCell G I.1 I.2 → ∑ v, Pa.coef I Za v * Pa.scalarAt I v y -
        ∑ m, cga I m * aga I m y = P₁.val I y - P₂.val I y)
    (hrb : ∃ P₁ P₂ : BasicProjection G R' CF, P₁.Ψ.D.budget ≤ X ∧ P₂.Ψ.D.budget ≤ X ∧
      P₁.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₂.HasChartsOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c₀'
        H' ∧
      P₁.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      P₂.CellEnergyOn {I | I ∈ cells ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
      ∀ I ∈ cells,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 → ∀ᵐ y ∂volume,
      y ∈ dyadicGridCell G I.1 I.2 → ∑ v, Pb.coef I Zb v * Pb.scalarAt I v y -
        ∑ m, cgb I m * agb I m y = P₁.val I y - P₂.val I y) :
    (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb hab
        hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
          hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam hYbm
            S hS hUa hUb hUa' hUb' η hsmall).ColumnRepBelow R' CF := by
  have hXc : X ≤ (baseActiveSetup κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib
      hka hkb hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb hdef Dc hDc hPac hPbc hcga hcgb Ya
        Yb hYam hYbm S hS hUa hUb hUa' hUb' η hsmall).colBudget := by
    refine hX.trans (le_of_eq ?_)
    change _ = 2 + (Fintype.card (Xi.Λ ⊕ Xk.Λ ⊕ (Wa ⊕ Ga) ⊕ (Wb ⊕ Gb)) : ℝ) * (1 + Dc)
    simp only [Fintype.card_sum]
    push_cast
    ring
  intro l
  rcases fin_four_cover hia.symm hka.symm hab hik hib hkb l with h | h | h | h <;> rw [h]
  · obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := hra
    refine ⟨P₁, P₂, h₁.trans hXc, h₂.trans hXc, c₁, c₂, e₁, e₂, fun I hI hIR => ?_⟩
    filter_upwards [hP I hI hIR] with y hy hyI
    rw [(baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb
          hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
            hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam
              hYbm S hS hUa hUb hUa' hUb' η hsmall hI a)]
    exact (baseB_a Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hia hka hab I y).trans (hy hyI)
  · obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := hri
    refine ⟨P₁, P₂, h₁.trans hXc, h₂.trans hXc, c₁, c₂, e₁, e₂, fun I hI hIR => ?_⟩
    filter_upwards [hP I hI hIR] with y hy hyI
    rw [(baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb
          hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
            hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam
              hYbm S hS hUa hUb hUa' hUb' η hsmall hI i)]
    exact (baseB_i Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hia hib I y).trans (hy hyI)
  · obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := hrk
    refine ⟨P₁, P₂, h₁.trans hXc, h₂.trans hXc, c₁, c₂, e₁, e₂, fun I hI hIR => ?_⟩
    filter_upwards [hP I hI hIR] with y hy hyI
    rw [(baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb
          hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
            hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam
              hYbm S hS hUa hUb hUa' hUb' η hsmall hI k)]
    exact (baseB_k Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hik hka hkb I y).trans (hy hyI)
  · obtain ⟨P₁, P₂, h₁, h₂, c₁, c₂, e₁, e₂, hP⟩ := hrb
    refine ⟨P₁, P₂, h₁.trans hXc, h₂.trans hXc, c₁, c₂, e₁, e₂, fun I hI hIR => ?_⟩
    filter_upwards [hP I hI hIR] with y hy hyI
    rw [(baseActiveSetup_B κ Xi Xk Pa Pb Za Zb cga aga cgb agb R cells hsub w hw hik hia hib hka hkb
          hab hagm hagb hbgm hbgb H' hXi hXk hPa hPb hga hgb
            hdef Dc hDc hPac hPbc hcga hcgb Ya Yb hYam
              hYbm S hS hUa hUb hUa' hUb' η hsmall hI b)]
    exact (baseB_b Xi Xk Pa Pb Za Zb cga aga cgb agb i k a b hib hkb hab I y).trans (hy hyI)

end BaseActiveSetupFacts

namespace AccSetup
variable {S : AccSetup}

theorem memLp_normalized_of_bound {a r : ℝ} (hr : 0 < r) {g : ℝ → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) : MemLp g 2 (normalizedIntervalMeasure a r) := by
  have := normalizedIntervalMeasure_probability a hr
  exact MemLp.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem U_measurable (S : AccSetup) (K I : ℤ × ℤ) :
    Measurable fun y => S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y :=
  (phys_measurable _ _ _).sub (S.cur_measurable K I)

theorem U_bound (S : AccSetup) (K I : ℤ × ℤ) :
    ∃ C, ∀ y, ‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := phys_bound (S := S) I (S.tree.st I).1 (S.tree.st I).2
  obtain ⟨C₂, h₂⟩ := S.cur_bound K I
  exact ⟨C₁ + C₂, fun y => (norm_sub_le _ _).trans (add_le_add (h₁ y) (h₂ y))⟩

theorem U_memLp (S : AccSetup) (K I : ℤ × ℤ) :
    MemLp (fun y => S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y) 2
      (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2) (dyadicGridLength S.G I.1)) := by
  obtain ⟨C, hC⟩ := S.U_bound K I
  exact memLp_normalized_of_bound (dyadicGridLength_pos _ _) (S.U_measurable K I) hC

/-- The length-weighted squared normalized norm of a basic side is its `L²(I)` energy. -/
theorem U_sq_eq (S : AccSetup) (K I : ℤ × ℤ) :
    dyadicGridLength S.G I.1 * (eLpNorm (fun y => S.phys I (S.tree.st I).1 (S.tree.st I).2 y -
      S.cur K I y) 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
        (dyadicGridLength S.G I.1))).toReal ^ 2 =
      ∫ y in S.cell I, ‖S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y‖ ^ 2 := by
  have hr := dyadicGridLength_pos S.G I.1
  rw [eLpNorm_normalized_toReal_sq hr (S.U_memLp K I), ← mul_assoc, mul_inv_cancel₀ hr.ne',
    one_mul]
  rfl

theorem Hyp.U_eLpNorm_le (h : S.Hyp) {K I : ℤ × ℤ} (hIc : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hIH : kernelHull S.G S.J S.N S.w I) :
    (eLpNorm (fun y => S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y) 2
      (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
        (dyadicGridLength S.G I.1))).toReal ≤ 2 := by
  have hr := dyadicGridLength_pos S.G I.1
  have h1 := S.U_sq_eq K I
  have h2 := h.U_sq_le (K := K) hIc hIH
  have h3 : (eLpNorm (fun y => S.phys I (S.tree.st I).1 (S.tree.st I).2 y - S.cur K I y) 2
      (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
        (dyadicGridLength S.G I.1))).toReal ^ 2 ≤ 2 ^ 2 := by
    have : dyadicGridLength S.G I.1 * (eLpNorm (fun y => S.phys I (S.tree.st I).1
        (S.tree.st I).2 y - S.cur K I y) 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1
          I.2) (dyadicGridLength S.G I.1))).toReal ^ 2 ≤ dyadicGridLength S.G I.1 * 2 ^ 2 := by
      rw [h1]; linarith
    exact le_of_mul_le_mul_left this hr
  exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg (by norm_num) two_ne_zero).mp h3

/-- The fine projections have normalized `L²` norm at most one on a coarse cell. -/
theorem Hyp.phys_eLpNorm_le (h : S.Hyp) {I : ℤ × ℤ} (hIc : I ∈ dyadicFiniteTree S.G S.J S.Nc)
    (hIH : kernelHull S.G S.J S.N S.w I) (a : ℕ → ℝ → ℂ) (n : ℕ) :
    eLpNorm (S.phys I a n) 2 (normalizedIntervalMeasure (dyadicGridLeft S.G I.1 I.2)
      (dyadicGridLength S.G I.1)) ≤ ENNReal.ofReal 1 := by
  have hr := dyadicGridLength_pos S.G I.1
  obtain ⟨C, hC⟩ := phys_bound (S := S) I a n
  have := cell_isFiniteMeasure S.G I.1 I.2
  refine eLpNorm_normalized_le_of_integral hr ?_ zero_le_one ?_
  · exact MemLp.of_bound (phys_measurable I a n).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  · rw [one_pow, one_mul]
    exact h.phys_sq_le hIc hIH a n

end AccSetup

/-! ### The base data on one root -/

/-- A family of cell functions that is a basic projection below every tree cell: the physical part
of the current projections of one column depth family whose root contains `J`, whose column
budget is at most `Bd` and whose columns available on tree cells are charts of order `c` and
complexity at most `Hc` there, applied to an augmented input of energy at most `CF |R|` on every
tree cell `R`. -/
def IsBasicOn (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (CF Bd : ℝ) (c : ℕ) (Hc : ℝ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ) (z : ℤ × ℤ → ℝ → ℂ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (Ψ : ColumnDepthFamily V) (Z : ColumnL2 V), Ψ.D.grid = G ∧
    dyadicGridCell G J.1 J.2 ⊆ dyadicGridCell G Ψ.D.root.1 Ψ.D.root.2 ∧ Ψ.D.budget ≤ Bd ∧
    (∀ c' ∈ dyadicFiniteTree G J N, c' ∈ Ψ.D.cells ∧ c'.1 ≤ Ψ.N ∧
      ∀ v ∈ Ψ.A.labels c', ∃ (d : ℕ) (Φ : QuadraticChartData d),
      QuadraticChartComplexity c Hc Φ ∧ IsBoundedQuadraticChart Φ ∧
      ∀ y ∈ dyadicGridCell G c'.1 c'.2, Ψ.D.scalar v y = quadraticChartAtom Φ y) ∧
    (∀ R ∈ dyadicFiniteTree G J N, kernelHull G J N w R → ∫ y in dyadicGridCell G R.1 R.2,
      ‖(Z : ℝ → ColumnHilbert V) y‖ ^ 2 ≤ CF * dyadicGridLength G R.1) ∧
    ∀ I, z I = Ψ.currentZ Z I

/-- The kernel hull of a subtree is the kernel hull of the tree restricted to the subtree. -/
theorem kernelHull_below_iff {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ}
    {w : ℤ × ℤ → ℝ × ℝ → ℂ} {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) {c : ℤ × ℤ}
    (hc : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G R.1 R.2) :
    kernelHull G R (dyadicRemainingDepth J N R) w c ↔ kernelHull G J N w c := by
  constructor
  · rintro ⟨c', hc', hsub, hw⟩
    exact ⟨c', ((dyadicFiniteTree_below_iff G J N hR c').mp hc').1, hsub, hw⟩
  · rintro ⟨c', hc', hsub, hw⟩
    exact ⟨c', (dyadicFiniteTree_below_iff G J N hR c').mpr ⟨hc', hsub.trans hc⟩, hsub, hw⟩

theorem IsBasicOn.basicProjection {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {CF Bd : ℝ} {c : ℕ}
    {Hc : ℝ} {w : ℤ × ℤ → ℝ × ℝ → ℂ} {z : ℤ × ℤ → ℝ → ℂ} (h : IsBasicOn G J N CF Bd c Hc w z)
    {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (hRH : kernelHull G J N w R) :
    ∃ P : BasicProjection G R CF, P.Ψ.D.budget ≤ Bd ∧
      P.HasChartsOn {c' | c' ∈ dyadicFiniteTree G J N} c Hc ∧
      P.CellEnergyOn {c' | c' ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w c'} ∧
      ∀ I, z I = P.val I := by
  obtain ⟨V, _, Ψ, Z, hG, hJ, hb, hch, hE, hz⟩ := h
  exact ⟨⟨V, Ψ, Z, hG, (((dyadicFiniteTree_mem_iff G J R N).mp hR).1).trans hJ,
    hE R hR hRH⟩, hb, fun c' hc' => hch c' hc', fun c' hc' => hE c' hc'.1 hc'.2, hz⟩

/-- Enlarging the column budget of a basic family. -/
theorem IsBasicOn.mono_budget {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {CF Bd Bd' : ℝ} {c : ℕ}
    {Hc : ℝ} {w : ℤ × ℤ → ℝ × ℝ → ℂ} {z : ℤ × ℤ → ℝ → ℂ} (h : IsBasicOn G J N CF Bd c Hc w z)
    (hB : Bd ≤ Bd') : IsBasicOn G J N CF Bd' c Hc w z := by
  obtain ⟨V, _, Ψ, Z, hG, hJ, hb, hch, hE, hz⟩ := h
  exact ⟨V, inferInstance, Ψ, Z, hG, hJ, hb.trans hB, hch, hE, hz⟩

/-- Enlarging the chart order and complexity of a basic family. -/
theorem IsBasicOn.mono_chart {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {CF Bd : ℝ} {c c' : ℕ}
    {Hc Hc' : ℝ} {w : ℤ × ℤ → ℝ × ℝ → ℂ} {z : ℤ × ℤ → ℝ → ℂ} (h : IsBasicOn G J N CF Bd c Hc w z)
    (hc : c ≤ c') (hH : Hc ≤ Hc') : IsBasicOn G J N CF Bd c' Hc' w z := by
  obtain ⟨V, _, Ψ, Z, hG, hJ, hb, hch, hE, hz⟩ := h
  refine ⟨V, inferInstance, Ψ, Z, hG, hJ, hb, fun c₁ hc₁ => ?_, hE, hz⟩
  obtain ⟨m1, m2, hch'⟩ := hch c₁ hc₁
  refine ⟨m1, m2, fun v hv => ?_⟩
  obtain ⟨d, Φ, h1, h2, h3⟩ := hch' v hv
  exact ⟨d, Φ, quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h1 hH) hc, h2,
    h3⟩

/-- A basic projection with zero input below any sub-cell of the root of a basic family. -/
theorem IsBasicOn.zeroProjection {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {CF Bd : ℝ} {c : ℕ}
    {Hc : ℝ} {w : ℤ × ℤ → ℝ × ℝ → ℂ} {z : ℤ × ℤ → ℝ → ℂ} (h : IsBasicOn G J N CF Bd c Hc w z)
    (hCF : 0 ≤ CF) {R : ℤ × ℤ} (hR : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G J.1 J.2) :
    ∃ P : BasicProjection G R CF, P.Ψ.D.budget ≤ Bd ∧
      P.HasChartsOn {c' | c' ∈ dyadicFiniteTree G J N} c Hc := by
  obtain ⟨V, _, Ψ, Z, hG, hJ, hb, hch, -, -⟩ := h
  refine ⟨⟨V, Ψ, 0, hG, hR.trans hJ, ?_⟩, hb, fun c' hc' => hch c' hc'⟩
  have : ∫ y in dyadicGridCell G R.1 R.2, ‖((0 : ColumnL2 V) : ℝ → ColumnHilbert V) y‖ ^ 2
      = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp
  rw [this]
  exact mul_nonneg hCF (dyadicGridLength_pos G R.1).le

section BaseRoot
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ c₁ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {a i k b : Fin 4} (Bp D : ℝ)
  (pkga : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b Bp D c₁)
  (pkgb : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) b i k a Bp D c₁)
  {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)



end BaseRoot
end TrilinearHT.Auto
end
