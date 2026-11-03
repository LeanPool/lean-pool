/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec112cFiniteBaseDataAssembly.ReplaceTuple

/-!
# Trilinear Hilbert transform: baseRoot
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
section BaseRoot
variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ c₁ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {a i k b : Fin 4} (Bp D : ℝ)
  (pkga : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b Bp D c₁)
  (pkgb : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) b i k a Bp D c₁)
  {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)

open scoped Classical in
private def BaseRootHsubrootStatement : Prop :=
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
    (hai : a ≠ i)
    (hak : a ≠ k)
    (hab : a ≠ b)
    (hik : i ≠ k)
    (hib : i ≠ b)
    (hkb : k ≠ b)
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
    (hw : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (Ka : ℤ × ℤ)
    (Kb : ℤ × ℤ)
    (R : ℤ × ℤ)
    (Xga : LowList G J N J c₀ H)
    (Xgb : LowList G J N J c₀ H)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (T : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀
      Ma (f a) w q ka c₂ Ba).Nc ∧ (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma
      (f a) w q ka c₂ Ba).tree.seg I = Ka ∧ (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0
      hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.seg I = Kb ∧ dyadicGridCell G I.1 I.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zga I y =
      Xga.val I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y)
    (_ : ∀ I ∈ T, kernelHull G J N w I)
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (c' : ℕ)
    (H' : ℝ)
    (_ : c₁ ≤ c')
    (_ : c₂ ≤ c')
    (Bd : ℝ)
    (cB : ℕ)
    (HB : ℝ)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zga)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zgb)
    (_ : cB ≤ c')
    (_ : HB ≤ H'),
  let Sa : AccSetup :=
    predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba
  let Sb : AccSetup :=
    predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb
  let Pa : PathColumnSystem Sa.G Sa.J Sa.N Sa.W :=
    Sa.system Ka
  let Pb : PathColumnSystem Sb.G Sb.J Sb.N Sb.W :=
    Sb.system Kb
  ∀ (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N),
  let Ya : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 -
      Xga.val I else baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I
  let Yb : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 -
      Xgb.val I else baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I
  ∀ (_ : ∀ I ∈ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I = fun (y : ℝ) => Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 y - Sa.cur Ka
      I y)
    (_ : ∀ I ∈ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I = fun (y : ℝ) => Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 y - Sb.cur Kb
      I y)
    (hYam : ∀ (I : ℤ × ℤ), Measurable (Ya I))
    (hYbm : ∀ (I : ℤ × ℤ), Measurable (Yb I))
    (hUa : ∀ (I : ℤ × ℤ), MemLp (Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ)
      => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ (I : ℤ × ℤ), MemLp (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ)
      => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ (I : ℤ × ℤ), (eLpNorm (Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (hUb' : ∀ (I : ℤ × ℤ), (eLpNorm (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (hsmall : ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (Ya I)
      (Xi.val I) (Xk.val I) (Yb I))‖ ≤ (4 : ℝ) * η₀)
    (hdefc : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c' H' Φ ∧
      IsBoundedQuadraticChart Φ)
    (hlowc : ∀ (X : LowList G J N J c₀ H), PathCharts G T (fun (I : ℤ × ℤ) (l : X.Λ) => X.atom I
      l) (fun (I : ℤ × ℤ) (l : X.Λ) => X.coef I l ≠ (0 : ℂ)) c' H')
    (hPac' : PathCharts G T (fun (I : ℤ × ℤ) (v : Sa.W) => Pa.scalarAt I v) (fun (I : ℤ × ℤ) (v :
      Sa.W) => v ∈ Pa.avail I) c' H')
    (hPbc' : PathCharts G T (fun (I : ℤ × ℤ) (v : Sb.W) => Pb.scalarAt I v) (fun (I : ℤ × ℤ) (v :
      Sb.W) => v ∈ Pb.avail I) c' H')
    (hDc : (1 : ℝ) ≤ √ε⁻¹)
    (hPac : ∀ I ∈ T, ∀ (v : Sa.W), ‖Pa.coef I Sa.Z v‖ ≤ √ε⁻¹)
    (hPbc : ∀ I ∈ T, ∀ (v : Sb.W), ‖Pb.coef I Sb.Z v‖ ≤ √ε⁻¹)
    (hsub : ∀ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2),
  let A : ActiveSetup κ c' :=
    baseActiveSetup κ Xi Xk Pa Pb Sa.Z Sb.Z Xga.coef (fun I l => Xga.atom I l) Xgb.coef
        (fun I l => Xgb.atom I l) R T hsub w (fun I _ => hw I) hik hai.symm hib hak.symm hkb hab
        (fun I m => Xga.atom_measurable I m) (fun I m y => Xga.atom_bound I m y)
        (fun I m => Xgb.atom_measurable I m) (fun I m y => Xgb.atom_bound I m y) H'
        (hlowc Xi) (hlowc Xk) hPac' hPbc' (hlowc Xga) (hlowc Xgb) hdefc (Real.sqrt ε⁻¹) hDc hPac
          hPbc
        Xga.coef_le Xgb.coef_le Ya Yb hYam hYbm 2 (by norm_num) hUa hUb hUa' hUb'
        (4 * η₀) hsmall
  ∀ (_ : ∀ (I : ℤ × ℤ), A.U a I = Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I)
    (_ : ∀ (I : ℤ × ℤ), A.U b I = Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I)
    (_ : ∀ (l : Fin (4 : ℕ)) (I : ℤ × ℤ), l ≠ a → l ≠ b → A.U l I = (0 : ℝ → ℂ))
    (_ : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G J.1 J.2)
    (_ : ∀ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ / (2 : ℝ)
      * (dyadicGridLength G I.1 * (eLpNorm (A.U a I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ) + dyadicGridLength G I.1 * (eLpNorm (A.U b I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ))),
  let XB : ℝ :=
    (2 : ℝ) + (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W +
      Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ)) : ℝ) * ((1 : ℝ) +
      √ε⁻¹)
  ∀ (_ : Bd ≤ XB)
    (_ : Pa.budget ≤ XB)
    (_ : Pb.budget ≤ XB),
  A.SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))


open scoped Classical in
private def BaseRootStage2Statement : Prop :=
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
    (hai : a ≠ i)
    (hak : a ≠ k)
    (hab : a ≠ b)
    (hik : i ≠ k)
    (hib : i ≠ b)
    (hkb : k ≠ b)
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
    (hw : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (Ka : ℤ × ℤ)
    (Kb : ℤ × ℤ)
    (_ : Ka ∈ (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      Ba).tree.roots)
    (_ : Kb ∈ (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      Bb).tree.roots)
    (R : ℤ × ℤ)
    (_ : R ∈ dyadicFiniteTree G J N)
    (Xga : LowList G J N J c₀ H)
    (Xgb : LowList G J N J c₀ H)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (Cga : ℝ)
    (Cgb : ℝ)
    (_ : (0 : ℝ) ≤ Cga)
    (_ : (0 : ℝ) ≤ Cgb)
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
      Xga.val I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y)
    (_ : ∀ I ∈ T, kernelHull G J N w I)
    (_ : (2 : ℝ) ≤ q)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ I ∈ T, ∀ (l : Fin (4 : ℕ)), eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      (1 : ℝ≥0∞))
    (_ : ∀ I ∈ T, eLpNorm (Xi.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (_ : ∀ I ∈ T, eLpNorm (Xk.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (η₀ : ℝ)
    (δa : ℝ)
    (δb : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : (0 : ℝ) ≤ δa)
    (_ : (0 : ℝ) ≤ δb)
    (_ : ∀ I ∈ T, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s' (slots4 a i k (f a - Xga.val I) (Xi.val I)
      (Xk.val I) (f b - Xgb.val I) s) (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val
      I) (f b - Xgb.val I) s') η₀)
    (_ : ∀ I ∈ T, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) a q (f
      a - (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).phys
      I ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      Ba).tree.st I).1 ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q
      ka c₂ Ba).tree.st I).2) δa)
    (_ : ∀ I ∈ T, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) b q (f
      b - (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).phys
      I ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      Bb).tree.st I).1 ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q
      kb c₂ Bb).tree.st I).2) δb)
    (c' : ℕ)
    (H' : ℝ)
    (_ : c₁ ≤ c')
    (_ : c₂ ≤ c')
    (Bd : ℝ)
    (cB : ℕ)
    (HB : ℝ)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zga)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zgb)
    (_ : cB ≤ c')
    (_ : HB ≤ H'),
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
  let S₀ : ℝ :=
    (1 : ℝ) + (↑(Fintype.card Xi.Λ) : ℝ) + (↑(Fintype.card Xk.Λ) : ℝ) + (↑(Fintype.card
      Xga.Λ) : ℝ) + (↑(Fintype.card Xgb.Λ) : ℝ)
  let Sp : ℝ :=
    (↑(Fintype.card Sa.W) : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let Pa : PathColumnSystem Sa.G Sa.J Sa.N Sa.W :=
    Sa.system Ka
  ∀ (_ : Pa = Sa.system Ka),
  let Pb : PathColumnSystem Sb.G Sb.J Sb.N Sb.W :=
    Sb.system Kb
  ∀ (_ : Pb = Sb.system Kb)
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N)
    (_ : (0 : ℝ) < S₀),
  let Ya : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 -
      Xga.val I else baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I
  ∀ (_ : Ya = fun (I : ℤ × ℤ) => if I ∈ T then Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 -
      Xga.val I else baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I),
  let Yb : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 -
      Xgb.val I else baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I
  ∀ (_ : Yb = fun (I : ℤ × ℤ) => if I ∈ T then Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 -
      Xgb.val I else baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I)
    (_ : ∀ (I : ℤ × ℤ), baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom I
      l) I = fun (y : ℝ) => Sa.cur Ka I y - Xga.val I y)
    (_ : ∀ (I : ℤ × ℤ), baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom I
      l) I = fun (y : ℝ) => Sb.cur Kb I y - Xgb.val I y)
    (_ : ∀ I ∈ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I = fun (y : ℝ) => Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 y - Sa.cur Ka
      I y)
    (_ : ∀ I ∈ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I = fun (y : ℝ) => Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 y - Sb.cur Kb
      I y)
    (_ : ∀ I ∉ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I = (0 : ℝ → ℂ))
    (_ : ∀ I ∉ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I = (0 : ℝ → ℂ))
    (hYam : ∀ (I : ℤ × ℤ), Measurable (Ya I))
    (hYbm : ∀ (I : ℤ × ℤ), Measurable (Yb I))
    (hUa : ∀ (I : ℤ × ℤ), MemLp (Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ)
      => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ (I : ℤ × ℤ), MemLp (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ)
      => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ (I : ℤ × ℤ), (eLpNorm (Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (hUb' : ∀ (I : ℤ × ℤ), (eLpNorm (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (_ : ∀ (X : LowList G J N J c₀ H), X = Xi ∨ X = Xk ∨ X = Xga ∨ X = Xgb → (↑(Fintype.card
      X.Λ) : ℝ) ≤ S₀)
    (_ : ∀ I ∈ T, eLpNorm (Ya I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (_ : ∀ I ∈ T, eLpNorm (Yb I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (_ : ∀ I ∈ T, ∀ (Fa Fb : ℝ → ℂ), Measurable Fa → Measurable Fb → eLpNorm Fa (2 : ℝ≥0∞)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≠
      ∞ → eLpNorm Fb (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1)) ≠ ∞ → ‖localProgressionForm (dyadicGridLength G I.1) (w
      I) (slots4 a i k Fa (Xi.val I) (Xk.val I) Fb)‖ ≤ (eLpNorm Fa (2 : ℝ≥0∞)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1))).toReal * (eLpNorm Fb (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft
      G I.1 I.2) (dyadicGridLength G I.1))).toReal * η₀)
    (hsmall : ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (Ya I)
      (Xi.val I) (Xk.val I) (Yb I))‖ ≤ (4 : ℝ) * η₀)
    (hdefc : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c' H' Φ ∧
      IsBoundedQuadraticChart Φ)
    (hlowc : ∀ (X : LowList G J N J c₀ H), PathCharts G T (fun (I : ℤ × ℤ) (l : X.Λ) => X.atom I
      l) (fun (I : ℤ × ℤ) (l : X.Λ) => X.coef I l ≠ (0 : ℂ)) c' H')
    (hPac' : PathCharts G T (fun (I : ℤ × ℤ) (v : Sa.W) => Pa.scalarAt I v) (fun (I : ℤ × ℤ) (v :
      Sa.W) => v ∈ Pa.avail I) c' H')
    (hPbc' : PathCharts G T (fun (I : ℤ × ℤ) (v : Sb.W) => Pb.scalarAt I v) (fun (I : ℤ × ℤ) (v :
      Sb.W) => v ∈ Pb.avail I) c' H')
    (hDc : (1 : ℝ) ≤ √ε⁻¹)
    (_ : ∀ (v : Sa.W), ε ≤ Sa.wt v)
    (_ : ∀ (v : Sb.W), ε ≤ Sb.wt v)
    (hPac : ∀ I ∈ T, ∀ (v : Sa.W), ‖Pa.coef I Sa.Z v‖ ≤ √ε⁻¹)
    (hPbc : ∀ I ∈ T, ∀ (v : Sb.W), ‖Pb.coef I Sb.Z v‖ ≤ √ε⁻¹)
    (hsub : ∀ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2),
  let A : ActiveSetup κ c' :=
    baseActiveSetup κ Xi Xk Pa Pb Sa.Z Sb.Z Xga.coef (fun I l => Xga.atom I l) Xgb.coef
        (fun I l => Xgb.atom I l) R T hsub w (fun I _ => hw I) hik hai.symm hib hak.symm hkb hab
        (fun I m => Xga.atom_measurable I m) (fun I m y => Xga.atom_bound I m y)
        (fun I m => Xgb.atom_measurable I m) (fun I m y => Xgb.atom_bound I m y) H'
        (hlowc Xi) (hlowc Xk) hPac' hPbc' (hlowc Xga) (hlowc Xgb) hdefc (Real.sqrt ε⁻¹) hDc hPac
          hPbc
        Xga.coef_le Xgb.coef_le Ya Yb hYam hYbm 2 (by norm_num) hUa hUb hUa' hUb'
        (4 * η₀) hsmall
  ∀ (_ : A = baseActiveSetup κ Xi Xk Pa Pb Sa.Z Sb.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) =>
      Xga.atom I l) Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom I l) R T hsub w
      (fun (I : ℤ × ℤ) (x : I ∈ T) => hw I) hik (Ne.symm hai) hib (Ne.symm hak) hkb hab
      (fun (I : ℤ × ℤ) (m : Xga.Λ) => LowList.atom_measurable Xga I m) (fun (I : ℤ × ℤ)
      (m : Xga.Λ) (y : ℝ) => LowList.atom_bound Xga I m y) (fun (I : ℤ × ℤ) (m : Xgb.Λ)
      => LowList.atom_measurable Xgb I m) (fun (I : ℤ × ℤ) (m : Xgb.Λ) (y : ℝ) =>
      LowList.atom_bound Xgb I m y) H' (hlowc Xi) (hlowc Xk) hPac' hPbc' (hlowc Xga)
      (hlowc Xgb) hdefc (√ε⁻¹) hDc hPac hPbc Xga.coef_le Xgb.coef_le Ya Yb hYam hYbm (2
      : ℝ) (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ
      Nat.cast_zero) (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl (2 : ℝ))) (Eq.refl
      true)) hUa hUb hUa' hUb' ((4 : ℝ) * η₀) hsmall)
    (_ : ∀ I ∈ T, A.Y I = slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))
    (_ : ∀ (I : ℤ × ℤ), A.U a I = Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I)
    (_ : ∀ (I : ℤ × ℤ), A.U b I = Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I)
    (_ : ∀ I ∈ T, A.z (3 : Fin (4 : ℕ)) I = slots4 a i k (A.U a I) (Xi.val I) (Xk.val I) (A.U
      b I))
    (_ : ∀ (l : Fin (4 : ℕ)) (I : ℤ × ℤ), l ≠ a → l ≠ b → A.U l I = (0 : ℝ → ℂ))
    (_ : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G J.1 J.2)
    (_ : ∀ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ / (2 : ℝ)
      * (dyadicGridLength G I.1 * (eLpNorm (A.U a I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ) + dyadicGridLength G I.1 * (eLpNorm (A.U b I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ))),
  let XB : ℝ :=
    (2 : ℝ) + (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W +
      Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ)) : ℝ) * ((1 : ℝ) +
      √ε⁻¹)
  ∀ (_ : XB = (2 : ℝ) + (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W +
      Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ)) : ℝ) * ((1 : ℝ) +
      √ε⁻¹))
    (_ : (0 : ℝ) ≤ √ε⁻¹)
    (_ : Bd ≤ XB)
    (_ : Pa.budget ≤ XB),
  ∃ (A : ActiveSetup κ c'), A.G = G ∧ A.R = R ∧ A.cells = T ∧ A.w = w ∧ A.a = a ∧ A.b
    = b ∧ A.H = H' ∧ A.Dc = √ε⁻¹ ∧ A.S = (2 : ℝ) ∧ A.η = (4 : ℝ) * η₀ ∧ Fintype.card
    A.L = Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W + Fintype.card
    Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) ∧ ∑ I ∈ T, dyadicGridLength G
    I.1 * ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (f a -
    Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I)) - A.Hf I (A.Y I)‖ ≤
    (↑(Fintype.card Xi.Λ) : ℝ) * (↑(Fintype.card Xk.Λ) : ℝ) * (Ea * ((2 : ℝ) * ((1 :
    ℝ) + Cgb) + (4 : ℝ))) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2, ‖(↑(↑Sa.input : ℝ
    →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2,
    ‖(dyadicGridCell G J.1 J.2).indicator (f b) y‖ ^ (2 : ℕ)) + (↑(Fintype.card Xi.Λ)
    : ℝ) * (↑(Fintype.card Xk.Λ) : ℝ) * (Eb * ((2 : ℝ) * ((2 : ℝ) *
    (compressionOneConst (Pa.rooted R) + (↑K₀ : ℝ)) + Cga) + (4 : ℝ))) * √(∫ (y : ℝ)
    in dyadicGridCell G R.1 R.2, ‖(↑(↑Sb.input : ℝ →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2 :
    ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2, ‖(dyadicGridCell G J.1
    J.2).indicator (f a) y‖ ^ (2 : ℕ)) ∧ (∀ I ∈ T, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' →
    PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' (A.Y I s)
    (A.Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (δa + δb) + ((1 : ℝ) + Sp) * δb)) ∧ (∀
    I ∈ T, ∀ (l : Fin (4 : ℕ)), (eLpNorm (A.Y I l) (2 : ℝ≥0∞) (A.μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ T, dyadicGridLength G I.1 * (eLpNorm (A.U l I)
    (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
    R.1) ∧ ∑ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ *
    ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G R.1) ∧ A.HasColumnRep (1 : ℝ) ∧
    A.SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))


open scoped Classical in
private def BaseRootStage1Statement : Prop :=
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
    (_ : R ∈ dyadicFiniteTree G J N)
    (Xga : LowList G J N J c₀ H)
    (Xgb : LowList G J N J c₀ H)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (Cga : ℝ)
    (Cgb : ℝ)
    (_ : (0 : ℝ) ≤ Cga)
    (_ : (0 : ℝ) ≤ Cgb)
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
      Xga.val I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y)
    (_ : ∀ I ∈ T, kernelHull G J N w I)
    (_ : (2 : ℝ) ≤ q)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ I ∈ T, ∀ (l : Fin (4 : ℕ)), eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      (1 : ℝ≥0∞))
    (_ : ∀ I ∈ T, eLpNorm (Xi.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (_ : ∀ I ∈ T, eLpNorm (Xk.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (η₀ : ℝ)
    (δa : ℝ)
    (δb : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : (0 : ℝ) ≤ δa)
    (_ : (0 : ℝ) ≤ δb)
    (_ : ∀ I ∈ T, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s' (slots4 a i k (f a - Xga.val I) (Xi.val I)
      (Xk.val I) (f b - Xgb.val I) s) (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val
      I) (f b - Xgb.val I) s') η₀)
    (_ : ∀ I ∈ T, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) a q (f
      a - (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).phys
      I ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      Ba).tree.st I).1 ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q
      ka c₂ Ba).tree.st I).2) δa)
    (_ : ∀ I ∈ T, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) b q (f
      b - (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).phys
      I ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      Bb).tree.st I).1 ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q
      kb c₂ Bb).tree.st I).2) δb)
    (c' : ℕ)
    (H' : ℝ)
    (_ : c₀ ≤ c')
    (_ : c₁ ≤ c')
    (_ : c₂ ≤ c')
    (_ : H ≤ H')
    (_ : D ≤ H')
    (_ : Ba ≤ H')
    (_ : Bb ≤ H')
    (_ : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ)
    (Bd : ℝ)
    (cB : ℕ)
    (HB : ℝ)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zga)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zgb)
    (_ : Bd ≤ (2 : ℝ) + (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ) : ℝ))
    (_ : cB ≤ c')
    (_ : HB ≤ H'),
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
  let S₀ : ℝ :=
    (1 : ℝ) + (↑(Fintype.card Xi.Λ) : ℝ) + (↑(Fintype.card Xk.Λ) : ℝ) + (↑(Fintype.card
      Xga.Λ) : ℝ) + (↑(Fintype.card Xgb.Λ) : ℝ)
  let Sp : ℝ :=
    (↑(Fintype.card Sa.W) : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let Pa : PathColumnSystem Sa.G Sa.J Sa.N Sa.W :=
    Sa.system Ka
  ∀ (_ : Pa = Sa.system Ka),
  let Pb : PathColumnSystem Sb.G Sb.J Sb.N Sb.W :=
    Sb.system Kb
  ∀ (_ : Pb = Sb.system Kb)
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N)
    (_ : (0 : ℝ) < S₀),
  let Ya : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 -
      Xga.val I else baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I
  ∀ (_ : Ya = fun (I : ℤ × ℤ) => if I ∈ T then Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 -
      Xga.val I else baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I),
  let Yb : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 -
      Xgb.val I else baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I
  ∀ (_ : Yb = fun (I : ℤ × ℤ) => if I ∈ T then Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 -
      Xgb.val I else baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I)
    (_ : ∀ (I : ℤ × ℤ), baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom I
      l) I = fun (y : ℝ) => Sa.cur Ka I y - Xga.val I y)
    (_ : ∀ (I : ℤ × ℤ), baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom I
      l) I = fun (y : ℝ) => Sb.cur Kb I y - Xgb.val I y)
    (_ : ∀ I ∈ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I = fun (y : ℝ) => Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 y - Sa.cur Ka
      I y)
    (_ : ∀ I ∈ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I = fun (y : ℝ) => Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 y - Sb.cur Kb
      I y)
    (_ : ∀ I ∉ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) => Xga.atom
      I l) I = (0 : ℝ → ℂ))
    (_ : ∀ I ∉ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) => Xgb.atom
      I l) I = (0 : ℝ → ℂ))
    (_ : ∀ (I : ℤ × ℤ), Measurable (Ya I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (Yb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ)
      => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ)
      => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (_ : ∀ (I : ℤ × ℤ), (eLpNorm (Ya I - baseHighB Pa Sa.Z Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (_ : ∀ (I : ℤ × ℤ), (eLpNorm (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (_ : ∀ (X : LowList G J N J c₀ H), X = Xi ∨ X = Xk ∨ X = Xga ∨ X = Xgb → (↑(Fintype.card
      X.Λ) : ℝ) ≤ S₀)
    (_ : ∀ I ∈ T, eLpNorm (Ya I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (_ : ∀ I ∈ T, eLpNorm (Yb I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (_ : ∀ I ∈ T, ∀ (Fa Fb : ℝ → ℂ), Measurable Fa → Measurable Fb → eLpNorm Fa (2 : ℝ≥0∞)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≠
      ∞ → eLpNorm Fb (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1)) ≠ ∞ → ‖localProgressionForm (dyadicGridLength G I.1) (w
      I) (slots4 a i k Fa (Xi.val I) (Xk.val I) Fb)‖ ≤ (eLpNorm Fa (2 : ℝ≥0∞)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1))).toReal * (eLpNorm Fb (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft
      G I.1 I.2) (dyadicGridLength G I.1))).toReal * η₀),
  ∃ (A : ActiveSetup κ c'), A.G = G ∧ A.R = R ∧ A.cells = T ∧ A.w = w ∧ A.a = a ∧ A.b
    = b ∧ A.H = H' ∧ A.Dc = √ε⁻¹ ∧ A.S = (2 : ℝ) ∧ A.η = (4 : ℝ) * η₀ ∧ Fintype.card
    A.L = Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W + Fintype.card
    Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) ∧ ∑ I ∈ T, dyadicGridLength G
    I.1 * ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (f a -
    Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I)) - A.Hf I (A.Y I)‖ ≤
    (↑(Fintype.card Xi.Λ) : ℝ) * (↑(Fintype.card Xk.Λ) : ℝ) * (Ea * ((2 : ℝ) * ((1 :
    ℝ) + Cgb) + (4 : ℝ))) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2, ‖(↑(↑Sa.input : ℝ
    →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2,
    ‖(dyadicGridCell G J.1 J.2).indicator (f b) y‖ ^ (2 : ℕ)) + (↑(Fintype.card Xi.Λ)
    : ℝ) * (↑(Fintype.card Xk.Λ) : ℝ) * (Eb * ((2 : ℝ) * ((2 : ℝ) *
    (compressionOneConst (Pa.rooted R) + (↑K₀ : ℝ)) + Cga) + (4 : ℝ))) * √(∫ (y : ℝ)
    in dyadicGridCell G R.1 R.2, ‖(↑(↑Sb.input : ℝ →ₘ[volume] ℂ) : ℝ → ℂ) y‖ ^ (2 :
    ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G R.1 R.2, ‖(dyadicGridCell G J.1
    J.2).indicator (f a) y‖ ^ (2 : ℕ)) ∧ (∀ I ∈ T, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' →
    PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' (A.Y I s)
    (A.Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (δa + δb) + ((1 : ℝ) + Sp) * δb)) ∧ (∀
    I ∈ T, ∀ (l : Fin (4 : ℕ)), (eLpNorm (A.Y I l) (2 : ℝ≥0∞) (A.μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ T, dyadicGridLength G I.1 * (eLpNorm (A.U l I)
    (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
    R.1) ∧ ∑ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ *
    ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G R.1) ∧ A.HasColumnRep (1 : ℝ) ∧
    A.SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))




private theorem baseRoot_hsubroot : BaseRootHsubrootStatement := by
  classical
  intro κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik hib hkb K₀ Ma Mb f
    w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb R Xga Xgb zga zgb T hT hTH η₀ hη₀ c' H' hc₁ hc₂ Bd cB HB
    hri hrk hrga hrgb hcB hHB Sa Sb Pa Pb hTtree Ya Yb hUaT hUbT hYam hYbm hUa hUb hUa' hUb'
    hsmall hdefc hlowc hPac' hPbc' hDc hPac hPbc hsub A hUa_eq hUb_eq hU0 hRJ hcell XB hBdX hPaX
    hPbX R' hR'
  change dyadicGridCell G R'.1 R'.2 ⊆ dyadicGridCell G R.1 R.2 at hR'
  have hR'pos := dyadicGridLength_pos G R'.1
  change (∀ l, ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
      dyadicGridLength G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1) ∧
    ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
      dyadicGridLength G I.1 * ‖A.Hf I (A.z 3 I)‖ ≤
        η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1) ∧ A.ColumnRepBelow R' 1
  by_cases hne : ∃ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2
  swap
  · -- no cell below `R'`
    simp only [not_exists, not_and] at hne
    have hempty : T.filter (fun I => dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2) =
        ∅ := Finset.filter_eq_empty_iff.mpr fun I hI => hne I hI
    rw [hempty]
    simp only [Finset.sum_empty]
    refine ⟨fun l => by positivity, by positivity, fun l => ?_⟩
    obtain ⟨P, hPb, hPch⟩ := hrga.zeroProjection zero_le_one (hR'.trans hRJ)
    have hPX := hPb.trans hBdX
    have hPc : P.HasChartsOn
        {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c' H' :=
      hPch.mono (fun I hI => hTtree I hI.1) hcB hHB
    have hPe : P.CellEnergyOn
        {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} := fun c hc =>
      absurd hc.2 (hne c hc.1)
    apply baseActiveSetup_columnRepBelow (hX := le_rfl)
      (hri := ⟨P, P, hPX, hPX, hPc, hPc, hPe, hPe, fun I hI hIR => absurd hIR (hne I hI)⟩)
      (hrk := ⟨P, P, hPX, hPX, hPc, hPc, hPe, hPe, fun I hI hIR => absurd hIR (hne I hI)⟩)
      (hra := ⟨P, P, hPX, hPX, hPc, hPc, hPe, hPe, fun I hI hIR => absurd hIR (hne I hI)⟩)
      (hrb := ⟨P, P, hPX, hPX, hPc, hPc, hPe, hPe, fun I hI hIR => absurd hIR (hne I hI)⟩)
  obtain ⟨I₀, hI₀, hI₀R'⟩ := hne
  have hR'tree : R' ∈ dyadicFiniteTree G J N := (dyadicFiniteTree_mem_iff G J R' N).mpr
    ⟨hR'.trans hRJ, (dyadicGridCell_depth_le_of_subset G I₀ R' hI₀R').trans
      ((dyadicFiniteTree_mem_iff G J I₀ N).mp (hTtree I₀ hI₀)).2⟩
  have hR'H : kernelHull G J N w R' := (hTH I₀ hI₀).mono hI₀R'
  have hmem : ∀ I ∈ T.filter (fun I => dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2),
      I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 := fun I hI =>
    Finset.mem_filter.mp hI
  have hside_a : ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
      dyadicGridLength G I.1 * (eLpNorm (A.U a I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun I hI => ?_))
      (hSa.basicSide hR'tree hR'H _ fun I hI =>
        ⟨(hT I (hmem I hI).1).1, (hT I (hmem I hI).1).2.1, (hmem I hI).2⟩)
    rw [hUa_eq, hUaT I (hmem I hI).1]
    exact Sa.U_sq_eq Ka I
  have hside_b : ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
      dyadicGridLength G I.1 * (eLpNorm (A.U b I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun I hI => ?_))
      (hSb.basicSide hR'tree hR'H _ fun I hI =>
        ⟨(hT I (hmem I hI).1).1, (hT I (hmem I hI).1).2.2.1, (hmem I hI).2⟩)
    rw [hUb_eq, hUbT I (hmem I hI).1]
    exact Sb.U_sq_eq Kb I
  refine ⟨fun l => ?_, ?_, ?_⟩
  · -- the basic sides
    by_cases hla : l = a
    · rw [hla]; exact hside_a
    by_cases hlb : l = b
    · rw [hlb]; exact hside_b
    refine le_trans (le_of_eq ?_) (mul_nonneg (by positivity) hR'pos.le)
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [hU0 l I hla hlb]
    simp
  · -- the two-`U` term
    calc ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
          dyadicGridLength G I.1 * ‖A.Hf I (A.z 3 I)‖
        ≤ ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
          η₀ / 2 * (dyadicGridLength G I.1 * (eLpNorm (A.U a I) 2 (A.μ I)).toReal ^ 2 +
            dyadicGridLength G I.1 * (eLpNorm (A.U b I) 2 (A.μ I)).toReal ^ 2) :=
          Finset.sum_le_sum fun I hI => hcell I (hmem I hI).1
      _ = η₀ / 2 * (∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
            dyadicGridLength G I.1 * (eLpNorm (A.U a I) 2 (A.μ I)).toReal ^ 2 +
          ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
            dyadicGridLength G I.1 * (eLpNorm (A.U b I) 2 (A.μ I)).toReal ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ η₀ / 2 * ((K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1 +
          (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1) := by gcongr
      _ = _ := by ring
  · -- the column representation below `R'`
    have hEa : ∫ y in dyadicGridCell G R'.1 R'.2, ‖(Sa.Z : ℝ → ColumnHilbert Sa.W) y‖ ^ 2 ≤
        1 * dyadicGridLength G R'.1 := by
      rw [one_mul]
      exact hSa.energy_cell_le hR'tree hR'H
    have hEb : ∫ y in dyadicGridCell G R'.1 R'.2, ‖(Sb.Z : ℝ → ColumnHilbert Sb.W) y‖ ^ 2 ≤
        1 * dyadicGridLength G R'.1 := by
      rw [one_mul]
      exact hSb.energy_cell_le hR'tree hR'H
    obtain ⟨Pga, hPgab, hPgac, hPgae, hPga⟩ := hrga.basicProjection hR'tree hR'H
    obtain ⟨Pgb, hPgbb, hPgbc, hPgbe, hPgb⟩ := hrgb.basicProjection hR'tree hR'H
    have hTs : {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ⊆
        {c | c ∈ dyadicFiniteTree G J N} := fun I hI => hTtree I hI.1
    have hTH' : {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ⊆
        {c | c ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w c} := fun I hI =>
      ⟨hTtree I hI.1, hTH I hI.1⟩
    have hpair : ∀ {X : ℤ × ℤ → ℝ → ℂ}, (∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧
        IsBasicOn G J N 1 Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ y ∂volume,
          y ∈ dyadicGridCell G I.1 I.2 → X I y = z₁ I y - z₂ I y) →
        ∃ P₁ P₂ : BasicProjection G R' 1, P₁.Ψ.D.budget ≤ XB ∧ P₂.Ψ.D.budget ≤ XB ∧
          P₁.HasChartsOn {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2}
            c' H' ∧
          P₂.HasChartsOn {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2}
            c' H' ∧
          P₁.CellEnergyOn {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
          P₂.CellEnergyOn {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} ∧
          ∀ I ∈ T,
          dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 → ∀ᵐ y ∂volume,
            y ∈ dyadicGridCell G I.1 I.2 → X I y = P₁.val I y - P₂.val I y := by
      intro X hX
      obtain ⟨z₁, z₂, h₁, h₂, h₃⟩ := hX
      obtain ⟨P₁, hb₁, hc₁, he₁, hP₁⟩ := h₁.basicProjection hR'tree hR'H
      obtain ⟨P₂, hb₂, hc₂, he₂, hP₂⟩ := h₂.basicProjection hR'tree hR'H
      refine ⟨P₁, P₂, hb₁.trans hBdX, hb₂.trans hBdX, hc₁.mono hTs hcB hHB,
        hc₂.mono hTs hcB hHB, he₁.mono hTH', he₂.mono hTH', fun I hI _ => ?_⟩
      filter_upwards [h₃ I hI] with y hy hyI
      rw [hy hyI, hP₁ I, hP₂ I]
    have hPach : (Pa.basicProjection hR'tree Sa.Z hEa).HasChartsOn
        {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c' H' := by
      intro c hc
      refine ⟨(dyadicFiniteTree_below_iff G J N hR'tree c).mpr ⟨hTtree c hc.1, hc.2⟩,
        ((dyadicFiniteTree_mem_iff G J c N).mp (hTtree c hc.1)).2, fun v hv => ?_⟩
      obtain ⟨d, Φ, h1, h2, h3⟩ := hPac'.1 c hc.1 v hv
      refine ⟨d, Φ, h1, h2, fun y hy => ?_⟩
      change Pa.scalar R' v y = _
      rw [Pa.scalar_eq (hTtree c hc.1) hc.2 hv hy]
      exact congrFun h3 y
    have hPbch : (Pb.basicProjection hR'tree Sb.Z hEb).HasChartsOn
        {I | I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2} c' H' := by
      intro c hc
      refine ⟨(dyadicFiniteTree_below_iff G J N hR'tree c).mpr ⟨hTtree c hc.1, hc.2⟩,
        ((dyadicFiniteTree_mem_iff G J c N).mp (hTtree c hc.1)).2, fun v hv => ?_⟩
      obtain ⟨d, Φ, h1, h2, h3⟩ := hPbc'.1 c hc.1 v hv
      refine ⟨d, Φ, h1, h2, fun y hy => ?_⟩
      change Pb.scalar R' v y = _
      rw [Pb.scalar_eq (hTtree c hc.1) hc.2 hv hy]
      exact congrFun h3 y
    apply baseActiveSetup_columnRepBelow (hX := le_rfl) (hri := hpair hri) (hrk := hpair hrk)
      (hra := ⟨Pa.basicProjection hR'tree Sa.Z hEa, Pga, hPaX, hPgab.trans hBdX, hPach,
        hPgac.mono hTs hcB hHB, fun c hc => by
          rw [one_mul]; exact hSa.energy_cell_le (hTtree c hc.1) (hTH c hc.1),
        hPgae.mono hTH', fun I hI hIR => ?_⟩)
      (hrb := ⟨Pb.basicProjection hR'tree Sb.Z hEb, Pgb, hPbX, hPgbb.trans hBdX, hPbch,
        hPgbc.mono hTs hcB hHB, fun c hc => by
          rw [one_mul]; exact hSb.energy_cell_le (hTtree c hc.1) (hTH c hc.1),
        hPgbe.mono hTH', fun I hI hIR => ?_⟩)
    · filter_upwards [Pa.basicProjection_val_ae hR'tree (hTtree I hI) hIR Sa.Z hEa,
        (hT I hI).2.2.2.2.1] with y h1 h2 hyI
      rw [← hPga I, h2 hyI]
      exact congrArg (· - Xga.val I y) (h1 hyI).symm
    · filter_upwards [Pb.basicProjection_val_ae hR'tree (hTtree I hI) hIR Sb.Z hEb,
        (hT I hI).2.2.2.2.2] with y h1 h2 hyI
      rw [← hPgb I, h2 hyI]
      exact congrArg (· - Xgb.val I y) (h1 hyI).symm



private theorem baseRoot_stage_2 : BaseRootStage2Statement := by
  classical
  intro κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik hib hkb hD1 K₀ Ma
    Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb hKa hKb R hR Xga Xgb zga zgb Cga Cgb hCga hCgb hzga
    hzgb T hT hTH hq hfm hfq hLi hLk η₀ δa δb hη₀ hδa hδb hpairs hsa hsb c' H' hc₁ hc₂ Bd cB HB
    hri hrk hrga hrgb hcB hHB Sa Sb Ea Eb S₀ Sp Pa hPa_def Pb hPb_def hTtree hS₀ Ya hYa_def Yb
    hYb_def hHBa hHBb hUaT hUbT hUaN hUbN hYam hYbm hUa hUb hUa' hUb' hcard hYaS hYbS hlowpair
    hsmall hdefc hlowc hPac' hPbc' hDc hwa hwb hPac hPbc hsub A hA hY hUa_eq hUb_eq hz3 hU0 hRJ
    hcell XB hXB hsq0 hBdX hPaX
  have hPbX : Pb.budget ≤ XB := by
    refine (Pb.budget_le hε0 hwb).trans ?_
    rw [← Real.sqrt_inv, hXB]
    have hs : (Fintype.card Sb.W : ℝ) ≤ ((Fintype.card Xi.Λ + Fintype.card Xk.Λ +
        (Fintype.card Sa.W + Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) :
          ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hs hsq0, hDc]
  have hsubroot : A.SubRootProps η₀ ((K₀ : ℝ) ^ 2) := by
    expose_names
    exact @baseRoot_hsubroot κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab
      hik hib hkb K₀ Ma Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb R Xga Xgb zga zgb T hT hTH η₀ hη₀
      c' H' hc₁ hc₂ Bd cB HB hri hrk hrga hrgb hcB hHB hTtree hUaT hUbT hYam hYbm hUa hUb hUa'
      hUb' hsmall hdefc hlowc hPac' hPbc' hDc hPac hPbc hsub hUa_eq hUb_eq hU0 hRJ hcell hBdX hPaX
      hPbX
  have hRpos := dyadicGridLength_pos G R.1
  have hfilt : T.filter (fun I => dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2) = T :=
    Finset.filter_true_of_mem hsub
  obtain ⟨hsideR, htwoR, hcolR⟩ := hsubroot R subset_rfl
  change (∀ l, ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2,
      dyadicGridLength G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R.1) at hsideR
  change ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2,
      dyadicGridLength G I.1 * ‖A.Hf I (A.z 3 I)‖ ≤
        η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G R.1) at htwoR
  rw [hfilt] at hsideR htwoR
  refine ⟨A, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, hsideR, htwoR,
    A.hasColumnRep_of_below hcolR, hsubroot⟩
  · -- the label count
    change Fintype.card (Xi.Λ ⊕ Xk.Λ ⊕ (Sa.W ⊕ Xga.Λ) ⊕ (Sb.W ⊕ Xgb.Λ)) = _
    simp only [Fintype.card_sum]
    ring
  · -- the replacement
    have hrep := replaceTuple κ Xi Xk Bp D pkga pkgb hε0 hε1 hai hak hab hik hib hkb hD1 K₀ Ma Mb
      f w q ka kb c₂ Ba Bb hSa hSb hw hKa hKb hR (fun I => Xga.val I) (fun I => Xgb.val I)
      zga zgb hCga hCgb (fun I => Xga.val_measurable I) (fun I => Xgb.val_measurable I)
      hzga hzgb T hT
    refine le_of_eq_of_le (Finset.sum_congr rfl fun I hI => ?_) hrep
    have e : A.Y I = slots4 a i k (Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 - Xga.val I)
        (Xi.val I) (Xk.val I) (Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 - Xgb.val I) := by
      rw [hY I hI]
      simp only [hYa_def, hYb_def, hI, ↓reduceIte]
    rw [e]
    rfl
  · -- pair smallness of the replaced tuple
    intro I hI s s' hss
    rw [hY I hI]
    simp only [hYa_def, hYb_def, hI, ↓reduceIte]
    have hXS : ∀ X : LowList G J N J c₀ H, X = Xi ∨ X = Xk ∨ X = Xga ∨ X = Xgb →
        ∀ y, ‖X.val I y‖ ≤ S₀ := fun X hX y => (X.val_bound I y).trans (hcard X hX)
    have hSp : 0 < Sp := by positivity
    exact slots4_pairSmall (dyadicGridLength_pos G I.1) (hw I) hq hai hak hab hik hib hkb hfm
      (hfq I hI) (Xi.val_measurable I) (Xk.val_measurable I) (Xga.val_measurable I)
      (Xgb.val_measurable I) (AccSetup.phys_measurable (S := Sa) I _ _)
      (AccSetup.phys_measurable (S := Sb) I _ _) hS₀ hSp (hXS Xi (by simp)) (hXS Xk (by simp))
      (hXS Xga (by simp)) (hXS Xgb (by simp))
      (fun y => (hSa.phys_sup hε0 hε1 (fun v => le_rfl) (hT I hI).1 (hTH I hI)
        (AccSetup.state_atoms (S := Sa) _ _) _ y).trans (le_add_of_nonneg_right zero_le_one))
      (fun y => hSb.phys_sup hε0 hε1 (fun v => le_rfl) (hT I hI).1 (hTH I hI)
        (AccSetup.state_atoms (S := Sb) _ _) _ y)
      hδa hδb (hsa I hI) (hsb I hI) (hpairs I hI) s s' hss
  · -- the sizes
    intro I hI l
    rw [hY I hI]
    have hr := dyadicGridLength_pos G I.1
    rcases fin_four_cover hai hak hab hik hib hkb l with rfl | rfl | rfl | rfl
    · rw [slots4_a]; exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (hYaS I hI)
    · rw [slots4_i hai]; exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (hLi I hI)
    · rw [slots4_k hak hik]; exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (hLk I hI)
    · rw [slots4_b hab hib hkb]; exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (hYbS I hI)



private theorem baseRoot_stage_1 : BaseRootStage1Statement := by
  classical
  intro κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik hib hkb hD1 K₀ Ma
    Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb hKa hKb R hR Xga Xgb zga zgb Cga Cgb hCga hCgb hzga
    hzgb T hT hTH hq hfm hfq hLi hLk η₀ δa δb hη₀ hδa hδb hpairs hsa hsb c' H' hc₀ hc₁ hc₂ hHH hDH
    hBa hBb hdef₀ Bd cB HB hri hrk hrga hrgb hBd hcB hHB Sa Sb Ea Eb S₀ Sp Pa hPa_def Pb hPb_def
    hTtree hS₀ Ya hYa_def Yb hYb_def hHBa hHBb hUaT hUbT hUaN hUbN hYam hYbm hUa hUb hUa' hUb'
    hcard hYaS hYbS hlowpair
  have hsmall : ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ 4 * η₀ := by
    intro I hI
    have ha := hYaS I hI
    have hb := hYbS I hI
    refine (hlowpair I hI (Ya I) (Yb I) (hYam I) (hYbm I)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)).trans ?_
    have ha' := ENNReal.toReal_le_of_le_ofReal (by norm_num) ha
    have hb' := ENNReal.toReal_le_of_le_ofReal (by norm_num) hb
    have := mul_le_mul ha' hb' ENNReal.toReal_nonneg (by norm_num)
    calc _ ≤ 2 * 2 * η₀ := mul_le_mul_of_nonneg_right this hη₀
      _ = _ := by ring
  -- path charts
  have hdefc : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c' H' Φ ∧
      IsBoundedQuadraticChart Φ := by
    obtain ⟨d, Φ, h1, h2⟩ := hdef₀
    exact ⟨d, Φ, quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h1 hHH) hc₀, h2⟩
  have hlowc : ∀ X : LowList G J N J c₀ H, PathCharts G T (fun I l => X.atom I l)
      (fun I l => X.coef I l ≠ 0) c' H' := fun X =>
    PathCharts.mono_c (((X.pathCharts T).mono (fun _ _ h => h) hHH)) hc₀
  have hPac' : PathCharts G T (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c' H' :=
    hSa.system_pathCharts Ka T (PathCharts.mono_c (((predSystem_pathCharts κ Xi Xk a i k b Bp D
      pkga hε0 hε1 T hTtree).mono (fun _ _ h => h) hDH)) hc₁) hc₂ hBa
  have hPbc' : PathCharts G T (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c' H' :=
    hSb.system_pathCharts Kb T (PathCharts.mono_c (((predSystem_pathCharts κ Xi Xk b i k a Bp D
      pkgb hε0 hε1 T hTtree).mono (fun _ _ h => h) hDH)) hc₁) hc₂ hBb
  -- coefficient bounds
  have hDc : 1 ≤ Real.sqrt ε⁻¹ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ((one_le_inv₀ hε0).mpr hε1)
  have hwa : ∀ v, ε ≤ Sa.wt v := by
    intro v; cases v with
    | inl v => exact le_rfl
    | inr m => exact hε1
  have hwb : ∀ v, ε ≤ Sb.wt v := by
    intro v; cases v with
    | inl v => exact le_rfl
    | inr m => exact hε1
  have hPac : ∀ I ∈ T, ∀ v, ‖Pa.coef I Sa.Z v‖ ≤ Real.sqrt ε⁻¹ := fun I hI v =>
    hSa.coef_le (hTtree I hI) (hTH I hI) hε0 hwa v
  have hPbc : ∀ I ∈ T, ∀ v, ‖Pb.coef I Sb.Z v‖ ≤ Real.sqrt ε⁻¹ := fun I hI v =>
    hSb.coef_le (hTtree I hI) (hTH I hI) hε0 hwb v
  have hsub : ∀ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 := fun I hI =>
    (hT I hI).2.2.2.1
  set! A := baseActiveSetup κ Xi Xk Pa Pb Sa.Z Sb.Z Xga.coef (fun I l => Xga.atom I l) Xgb.coef
    (fun I l => Xgb.atom I l) R T hsub w (fun I _ => hw I) hik hai.symm hib hak.symm hkb hab
    (fun I m => Xga.atom_measurable I m) (fun I m y => Xga.atom_bound I m y)
    (fun I m => Xgb.atom_measurable I m) (fun I m y => Xgb.atom_bound I m y) H'
    (hlowc Xi) (hlowc Xk) hPac' hPbc' (hlowc Xga) (hlowc Xgb) hdefc (Real.sqrt ε⁻¹) hDc hPac hPbc
    Xga.coef_le Xgb.coef_le Ya Yb hYam hYbm 2 (by norm_num) hUa hUb hUa' hUb'
    (4 * η₀) hsmall with hA
  have hY : ∀ I ∈ T, A.Y I = slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I) := fun I hI =>
    baseActiveSetup_Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ hI
  have hUa_eq : ∀ I, A.U a I = Ya I - baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I :=
    fun I => baseActiveSetup_U_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I
  have hUb_eq : ∀ I, A.U b I = Yb I - baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I :=
    fun I => baseActiveSetup_U_b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I
  have hz3 : ∀ I ∈ T, A.z 3 I = slots4 a i k (A.U a I) (Xi.val I) (Xk.val I) (A.U b I) :=
    fun I hI => by
      rw [hUa_eq, hUb_eq]
      exact baseActiveSetup_z3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI
  have hU0 : ∀ l I, l ≠ a → l ≠ b → A.U l I = 0 := by
    intro l I h1 h2
    change (if l = a then _ else if l = b then _ else 0) = 0
    simp only [h1, h2, ↓reduceIte]
  have hRJ : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G J.1 J.2 :=
    ((dyadicFiniteTree_mem_iff G J R N).mp hR).1
  -- the per-cell two-`U` bound
  have hcell : ∀ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z 3 I)‖ ≤
      η₀ / 2 * (dyadicGridLength G I.1 * (eLpNorm (A.U a I) 2 (A.μ I)).toReal ^ 2 +
        dyadicGridLength G I.1 * (eLpNorm (A.U b I) 2 (A.μ I)).toReal ^ 2) := by
    intro I hI
    have hr := dyadicGridLength_pos G I.1
    rw [hz3 I hI]
    have h := hlowpair I hI (A.U a I) (A.U b I) (A.U_meas a I) (A.U_meas b I)
      (A.U_L2 a I).eLpNorm_ne_top (A.U_L2 b I).eLpNorm_ne_top
    set x := (eLpNorm (A.U a I) 2 (A.μ I)).toReal
    set y := (eLpNorm (A.U b I) 2 (A.μ I)).toReal
    have hxy : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith only [sq_nonneg (x - y)]
    calc dyadicGridLength G I.1 * ‖A.Hf I (slots4 a i k (A.U a I) (Xi.val I) (Xk.val I)
          (A.U b I))‖ ≤ dyadicGridLength G I.1 * (x * y * η₀) :=
          mul_le_mul_of_nonneg_left h hr.le
      _ ≤ dyadicGridLength G I.1 * ((x ^ 2 + y ^ 2) / 2 * η₀) := by gcongr
      _ = _ := by ring
  -- the sub-root properties
  -- the column budgets of the basic projections
  set! XB : ℝ := 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W +
    Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) : ℕ) : ℝ) *
      (1 + Real.sqrt ε⁻¹) with hXB
  have hsq0 : 0 ≤ Real.sqrt ε⁻¹ := Real.sqrt_nonneg _
  have hBdX : Bd ≤ XB := by
    refine hBd.trans ?_
    have hs : ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
        Fintype.card Xgb.Λ : ℕ) : ℝ) ≤ ((Fintype.card Xi.Λ + Fintype.card Xk.Λ +
          (Fintype.card Sa.W + Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) :
            ℕ) : ℝ) := by exact_mod_cast (by omega)
    have h0 : (0 : ℝ) ≤ ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Sa.W +
        Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [hXB]
    nlinarith only [mul_nonneg h0 hsq0, hs]
  have hPaX : Pa.budget ≤ XB := by
    refine (Pa.budget_le hε0 hwa).trans ?_
    rw [← Real.sqrt_inv, hXB]
    have hs : (Fintype.card Sa.W : ℝ) ≤ ((Fintype.card Xi.Λ + Fintype.card Xk.Λ +
        (Fintype.card Sa.W + Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) :
          ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hs hsq0, hDc]
  expose_names
  exact @baseRoot_stage_2 κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik
    hib hkb hD1 K₀ Ma Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb hKa hKb R hR Xga Xgb zga zgb Cga
    Cgb hCga hCgb hzga hzgb T hT hTH hq hfm hfq hLi hLk η₀ δa δb hη₀ hδa hδb hpairs hsa hsb c' H'
    hc₁ hc₂ Bd cB HB hri hrk hrga hrgb hcB hHB hPa_def hPb_def hTtree hS₀ hYa_def hYb_def hHBa
    hHBb hUaT hUbT hUaN hUbN hYam hYbm hUa hUb hUa' hUb' hcard hYaS hYbS hlowpair hsmall hdefc
    hlowc hPac' hPbc' hDc hwa hwb hPac hPbc hsub hA hY hUa_eq hUb_eq hz3 hU0 hRJ hcell hXB hsq0
    hBdX hPaX


/-- Blueprint prop:base (one root): on the cells `T` of a pair of accurate-fit segments below a
common root `R`, the replaced tuple `eq:Y` is packaged as an active setup: the replacement error of
`replaceTuple`, pair smallness of every pair of `Y`, bounded normalized sizes, the basic-side
estimate `eq:basic-side` and the two-`U` term. -/
theorem baseRoot (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b)
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
    (Xga Xgb : LowList G J N J c₀ H) (zga zgb : ℤ × ℤ → ℝ → ℂ) {Cga Cgb : ℝ} (hCga : 0 ≤ Cga)
    (hCgb : 0 ≤ Cgb)
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
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zga I y = Xga.val I y) ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y))
    (hTH : ∀ I ∈ T, kernelHull G J N w I) (hRH : kernelHull G J N w R)
    (hq : 2 ≤ q) (hfm : ∀ l, Measurable (f l))
    (hfq : ∀ I ∈ T, ∀ l, eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1)
    (hLi : ∀ I ∈ T, eLpNorm (Xi.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2)
    (hLk : ∀ I ∈ T, eLpNorm (Xk.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2)
    (hLga : ∀ I ∈ T, eLpNorm (Xga.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1)
    (hLgb : ∀ I ∈ T, eLpNorm (Xgb.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1)
    {η₀ δa δb : ℝ} (hη₀ : 0 ≤ η₀) (hδa : 0 ≤ δa) (hδb : 0 ≤ δb)
    (hpairs : ∀ I ∈ T, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s'
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s)
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s') η₀)
    (hsa : ∀ I ∈ T, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) a q
      (f a - (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).phys I
        ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.st I).1
        ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.st I).2)
      δa)
    (hsb : ∀ I ∈ T, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) b q
      (f b - (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).phys I
        ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.st I).1
        ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.st I).2)
      δb)
    {c' : ℕ} {H' : ℝ} (hc₀ : c₀ ≤ c') (hc₁ : c₁ ≤ c') (hc₂ : c₂ ≤ c') (hHH : H ≤ H')
    (hDH : D ≤ H') (hBa : Ba ≤ H') (hBb : Bb ≤ H')
    (hdef₀ : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ)
    {Bd : ℝ} {cB : ℕ} {HB : ℝ}
    (hri : ∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧ IsBasicOn G J N 1 Bd cB HB w z₂ ∧
      ∀ I ∈ T, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (hrk : ∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧ IsBasicOn G J N 1 Bd cB HB w z₂ ∧
      ∀ I ∈ T, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (hrga : IsBasicOn G J N 1 Bd cB HB w zga) (hrgb : IsBasicOn G J N 1 Bd cB HB w zgb)
    (hBd : Bd ≤ 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ : ℕ) : ℝ)) (hcB : cB ≤ c') (hHB : HB ≤ H') :
    let Sa := predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba
    let Sb := predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb
    let Ea := 2 * Real.exp (-Bp) * (2 * (compressionOneConst ((Sa.system Ka).rooted R) + K₀) + 1)
      + D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)
    let Eb := 2 * Real.exp (-Bp) * (2 * (compressionOneConst ((Sb.system Kb).rooted R) + K₀) + 1)
      + D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)
    let S₀ : ℝ := 1 + Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ
    let Sp : ℝ := Fintype.card Sa.W * Real.sqrt (2 ^ K₀ / ε) + 1
    ∃ A : ActiveSetup κ c', A.G = G ∧ A.R = R ∧ A.cells = T ∧ A.w = w ∧ A.a = a ∧ A.b = b ∧
      A.H = H' ∧ A.Dc = Real.sqrt ε⁻¹ ∧ A.S = 2 ∧ A.η = 4 * η₀ ∧
      Fintype.card A.L = Fintype.card Xi.Λ + Fintype.card Xk.Λ +
        (Fintype.card Sa.W + Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) ∧
      ∑ I ∈ T, dyadicGridLength G I.1 *
        ‖localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I)) -
          A.Hf I (A.Y I)‖ ≤
        (Fintype.card Xi.Λ * Fintype.card Xk.Λ) * (Ea * (2 * (1 + Cgb) + 4)) *
            Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(Sa.input : ℝ → ℂ) y‖ ^ 2) *
            Real.sqrt (∫ y in dyadicGridCell G R.1 R.2,
              ‖(dyadicGridCell G J.1 J.2).indicator (f b) y‖ ^ 2) +
          (Fintype.card Xi.Λ * Fintype.card Xk.Λ) *
            (Eb * (2 * (2 * (compressionOneConst ((Sa.system Ka).rooted R) + K₀) + Cga) + 4)) *
            Real.sqrt (∫ y in dyadicGridCell G R.1 R.2, ‖(Sb.input : ℝ → ℂ) y‖ ^ 2) *
            Real.sqrt (∫ y in dyadicGridCell G R.1 R.2,
              ‖(dyadicGridCell G J.1 J.2).indicator (f a) y‖ ^ 2) ∧
      (∀ I ∈ T, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
        (w I) s s' (A.Y I s) (A.Y I s') (η₀ + (2 + 2 * S₀) * (δa + δb) + (1 + Sp) * δb)) ∧
      (∀ I ∈ T, ∀ l, (eLpNorm (A.Y I l) 2 (A.μ I)).toReal ≤ 2) ∧
      (∀ l, ∑ I ∈ T, dyadicGridLength G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R.1) ∧
      ∑ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z 3 I)‖ ≤
        η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G R.1) ∧
      A.HasColumnRep 1 ∧ A.SubRootProps η₀ ((K₀ : ℝ) ^ 2) := by
  intro Sa Sb Ea Eb S₀ Sp
  classical
  set Pa := Sa.system Ka with hPa_def
  set! Pb := Sb.system Kb with hPb_def
  have hTtree : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N := fun I hI =>
    AccSetup.coarse_tree hSa (hT I hI).1
  have hS₀ : 0 < S₀ := by positivity
  -- the replaced high inputs
  set! Ya : ℤ × ℤ → ℝ → ℂ := fun I => if I ∈ T then
    Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 - Xga.val I
    else baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I with hYa_def
  set! Yb : ℤ × ℤ → ℝ → ℂ := fun I => if I ∈ T then
    Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 - Xgb.val I
    else baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I with hYb_def
  have hHBa : ∀ I, baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I =
      fun y => Sa.cur Ka I y - Xga.val I y := fun I => rfl
  have hHBb : ∀ I, baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I =
      fun y => Sb.cur Kb I y - Xgb.val I y := fun I => rfl
  have hUaT : ∀ I ∈ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I =
      fun y => Sa.phys I (Sa.tree.st I).1 (Sa.tree.st I).2 y - Sa.cur Ka I y := by
    intro I hI; funext y
    simp only [hYa_def, hI, ↓reduceIte, hHBa, Pi.sub_apply]; ring
  have hUbT : ∀ I ∈ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I =
      fun y => Sb.phys I (Sb.tree.st I).1 (Sb.tree.st I).2 y - Sb.cur Kb I y := by
    intro I hI; funext y
    simp only [hYb_def, hI, ↓reduceIte, hHBb, Pi.sub_apply]; ring
  have hUaN : ∀ I ∉ T, Ya I - baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I = 0 := by
    intro I hI; simp only [hYa_def, hI, ↓reduceIte, sub_self]
  have hUbN : ∀ I ∉ T, Yb I - baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I = 0 := by
    intro I hI; simp only [hYb_def, hI, ↓reduceIte, sub_self]
  have hYam : ∀ I, Measurable (Ya I) := by
    intro I
    by_cases hI : I ∈ T
    · simp only [hYa_def, hI, ↓reduceIte]
      exact (AccSetup.phys_measurable (S := Sa) I _ _).sub (Xga.val_measurable I)
    · simp only [hYa_def, hI, ↓reduceIte, hHBa]
      exact (Sa.cur_measurable Ka I).sub (Xga.val_measurable I)
  have hYbm : ∀ I, Measurable (Yb I) := by
    intro I
    by_cases hI : I ∈ T
    · simp only [hYb_def, hI, ↓reduceIte]
      exact (AccSetup.phys_measurable (S := Sb) I _ _).sub (Xgb.val_measurable I)
    · simp only [hYb_def, hI, ↓reduceIte, hHBb]
      exact (Sb.cur_measurable Kb I).sub (Xgb.val_measurable I)
  have hUa : ∀ I, MemLp (Ya I - baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) := by
    intro I
    by_cases hI : I ∈ T
    · rw [hUaT I hI]; exact Sa.U_memLp Ka I
    · rw [hUaN I hI]; exact MemLp.zero
  have hUb : ∀ I, MemLp (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) := by
    intro I
    by_cases hI : I ∈ T
    · rw [hUbT I hI]; exact Sb.U_memLp Kb I
    · rw [hUbN I hI]; exact MemLp.zero
  have hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Sa.Z Xga.coef (fun I l => Xga.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal ≤ 2 := by
    intro I
    by_cases hI : I ∈ T
    · rw [hUaT I hI]; exact hSa.U_eLpNorm_le (hT I hI).1 (hTH I hI)
    · rw [hUaN I hI]; simp
  have hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Sb.Z Xgb.coef (fun I l => Xgb.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal ≤ 2 := by
    intro I
    by_cases hI : I ∈ T
    · rw [hUbT I hI]; exact hSb.U_eLpNorm_le (hT I hI).1 (hTH I hI)
    · rw [hUbN I hI]; simp
  -- sizes of the replaced inputs
  have hsize : ∀ (S : AccSetup) (_ : S.Hyp) (X : LowList G J N J c₀ H) (I : ℤ × ℤ),
      S.G = G → I ∈ dyadicFiniteTree S.G S.J S.Nc → kernelHull S.G S.J S.N S.w I →
      eLpNorm (X.val I) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1)) ≤ ENNReal.ofReal 1 →
      eLpNorm (S.phys I (S.tree.st I).1 (S.tree.st I).2 - X.val I) 2
        (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2 := by
    intro S hS X I hG hIc hIH hX
    subst hG
    refine (eLpNorm_sub_le (by norm_num)).trans ?_
    rw [show (2 : ℝ) = 1 + 1 by norm_num, ENNReal.ofReal_add zero_le_one zero_le_one]
    exact add_le_add (hS.phys_eLpNorm_le hIc hIH _ _) hX
  have hcard : ∀ (X : LowList G J N J c₀ H), X = Xi ∨ X = Xk ∨ X = Xga ∨ X = Xgb →
      (Fintype.card X.Λ : ℝ) ≤ S₀ := by
    have h1 : (0 : ℝ) ≤ Fintype.card Xi.Λ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Fintype.card Xk.Λ := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ Fintype.card Xga.Λ := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ Fintype.card Xgb.Λ := Nat.cast_nonneg _
    rintro X (rfl | rfl | rfl | rfl) <;> simp only [S₀] <;> linarith
  have hYaS : ∀ I ∈ T, eLpNorm (Ya I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      ENNReal.ofReal 2 := by
    intro I hI
    simp only [hYa_def, hI, ↓reduceIte]
    exact hsize Sa hSa Xga I rfl (hT I hI).1 (hTH I hI) (hLga I hI)
  have hYbS : ∀ I ∈ T, eLpNorm (Yb I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      ENNReal.ofReal 2 := by
    intro I hI
    simp only [hYb_def, hI, ↓reduceIte]
    exact hsize Sb hSb Xgb I rfl (hT I hI).1 (hTH I hI) (hLgb I hI)
  -- the full form on a cell is small by pair smallness of the low pair
  have hlowpair : ∀ I ∈ T, ∀ (Fa Fb : ℝ → ℂ), Measurable Fa → Measurable Fb →
      eLpNorm Fa 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1)) ≠ ⊤ →
      eLpNorm Fb 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1)) ≠ ⊤ →
      ‖localProgressionForm (dyadicGridLength G I.1) (w I)
        (slots4 a i k Fa (Xi.val I) (Xk.val I) Fb)‖ ≤
        (eLpNorm Fa 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
          (dyadicGridLength G I.1))).toReal *
        (eLpNorm Fb 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
          (dyadicGridLength G I.1))).toReal * η₀ := by
    intro I hI Fa Fb hFa hFb hfa hfb
    have hp := hpairs I hI i k hik
    rw [slots4_i hai, slots4_k hak hik] at hp
    set F := slots4 a i k Fa (Xi.val I) (Xk.val I) Fb with hF_def
    have hFe : slotPair F i k (Xi.val I) (Xk.val I) = F := by
      unfold slotPair
      rw [show Xi.val I = F i from (slots4_i hai _ _ _ _).symm,
        show Xk.val I = F k from (slots4_k hak hik _ _ _ _).symm,
        Function.update_eq_self, Function.update_eq_self]
    have hFm : ∀ l, Measurable (F l) := by
      intro l
      rcases fin_four_cover hai hak hab hik hib hkb l with rfl | rfl | rfl | rfl
      · rw [hF_def, slots4_a]; exact hFa
      · rw [hF_def, slots4_i hai]; exact Xi.val_measurable I
      · rw [hF_def, slots4_k hak hik]; exact Xk.val_measurable I
      · rw [hF_def, slots4_b hab hib hkb]; exact hFb
    have := PairSmall.le_norm_mul hik hη₀ hp hFm hab hai hak hib.symm hkb.symm
      (by rw [hF_def, slots4_a]; exact hfa) (by rw [hF_def, slots4_b hab hib hkb]; exact hfb)
    rw [hFe, hF_def, slots4_a, slots4_b hab hib hkb] at this
    exact this
  expose_names
  exact @baseRoot_stage_1 κ G J N c₀ c₁ H Xi Xk a i k b Bp D pkga pkgb ε hε0 hε1 hai hak hab hik
    hib hkb hD1 K₀ Ma Mb f w q ka kb c₂ Ba Bb hSa hSb hw Ka Kb hKa hKb R hR Xga Xgb zga zgb Cga
    Cgb hCga hCgb hzga hzgb T hT hTH hq hfm hfq hLi hLk η₀ δa δb hη₀ hδa hδb hpairs hsa hsb c' H'
    hc₀ hc₁ hc₂ hHH hDH hBa hBb hdef₀ Bd cB HB hri hrk hrga hrgb hBd hcB hHB hPa_def hPb_def
    hTtree hS₀ hYa_def hYb_def hHBa hHBb hUaT hUbT hUaN hUbN hYam hYbm hUa hUb hUa' hUb' hcard
    hYaS hYbS hlowpair

end BaseRoot

namespace LowList
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ : ℕ} {H : ℝ}

/-! ### Re-rooting low lists at a tree cell -/

/-- A low list below a tree cell `R` as a low list on the tree below `R`. -/
noncomputable def reroot (X : LowList G J N R c₀ H) (hR : R ∈ dyadicFiniteTree G J N) :
    LowList G R (dyadicRemainingDepth J N R) R c₀ H where
  Λ := X.Λ
  coef := X.coef
  coef_le := X.coef_le
  avail := X.avail
  coef_avail := X.coef_avail
  avail_mono := fun c d l hc hd hcd h => X.avail_mono c d l
    ((dyadicFiniteTree_below_iff G J N hR c).mp hc).1
    ((dyadicFiniteTree_below_iff G J N hR d).mp hd).1 hcd h
  birth := X.birth
  dim := X.dim
  chart := X.chart
  birth_spec := fun I l h => by
    obtain ⟨h1, h2, h3⟩ := X.birth_spec I l h
    exact ⟨h1, (dyadicFiniteTree_below_iff G J N hR _).mpr ⟨h2, h3⟩, h3⟩
  avail_birth := X.avail_birth
  birth_canon' := X.birth_canon'
  one_le_dim := X.one_le_dim
  complexity := X.complexity
  bounded := X.bounded

theorem reroot_val (X : LowList G J N R c₀ H) (hR : R ∈ dyadicFiniteTree G J N) (I : ℤ × ℤ)
    (y : ℝ) : (X.reroot hR).val I y = X.val I y := rfl

theorem reroot_card (X : LowList G J N R c₀ H) (hR : R ∈ dyadicFiniteTree G J N) :
    Fintype.card (X.reroot hR).Λ = Fintype.card X.Λ := rfl

end LowList

/-! ### Packing of the common refinement of two segment families -/

/-- The deeper of two roots. -/
def deeperRoot (K K' : ℤ × ℤ) : ℤ × ℤ := if K'.1 ≤ K.1 then K else K'

/-- Each cell lies in the deeper of its two segment roots. -/
theorem cell_subset_deeperRoot (G : RealDyadicGrid) {I K K' : ℤ × ℤ}
    (hK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2)
    (hK' : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K'.1 K'.2) :
    dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (deeperRoot K K').1 (deeperRoot K K').2 := by
  unfold deeperRoot; split_ifs
  · exact hK
  · exact hK'

/-- The deeper root lies in the other one. -/
theorem deeperRoot_subset (G : RealDyadicGrid) {I K K' : ℤ × ℤ}
    (hK : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K.1 K.2)
    (hK' : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G K'.1 K'.2) :
    dyadicGridCell G (deeperRoot K K').1 (deeperRoot K K').2 ⊆ dyadicGridCell G K.1 K.2 ∧
      dyadicGridCell G (deeperRoot K K').1 (deeperRoot K K').2 ⊆ dyadicGridCell G K'.1 K'.2 := by
  have hx := dyadicGridCell_left_mem G I.1 I.2
  unfold deeperRoot; split_ifs with h
  · exact ⟨le_rfl, dyadicGridCell_subset_of_common_point G (hK hx) (hK' hx) h⟩
  · exact ⟨dyadicGridCell_subset_of_common_point G (hK' hx) (hK hx) (by omega), le_rfl⟩

/-- Blueprint prop:base (common refinement of two restart families): summing the deeper root
over the occurring pairs of segments costs at most the two root lengths. -/
theorem sum_deeperRoot_le (G : RealDyadicGrid) (Tc Ra Rb : Finset (ℤ × ℤ))
    (sa sb : ℤ × ℤ → ℤ × ℤ)
    (hsa : ∀ I ∈ Tc, sa I ∈ Ra ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (sa I).1 (sa I).2 ∧
      ∀ L ∈ Ra, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G L.1 L.2 → L.1 ≤ (sa I).1)
    (hsb : ∀ I ∈ Tc, sb I ∈ Rb ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (sb I).1 (sb I).2 ∧
      ∀ L ∈ Rb, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G L.1 L.2 → L.1 ≤ (sb I).1) :
    ∑ p ∈ Tc.image (fun I => (sa I, sb I)), dyadicGridLength G (deeperRoot p.1 p.2).1 ≤
      dyadicRootLength G Ra + dyadicRootLength G Rb := by
  classical
  set P := Tc.image (fun I => (sa I, sb I))
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.2.1 ≤ p.1.1)
    (fun p => dyadicGridLength G (deeperRoot p.1 p.2).1)
  rw [← hsplit]
  have hpos : ∀ c : ℤ × ℤ, 0 ≤ dyadicGridLength G c.1 := fun c => (dyadicGridLength_pos G c.1).le
  -- a pair is determined by its deeper root
  have key : ∀ I ∈ Tc, ∀ I' ∈ Tc, ∀ (sx sy : ℤ × ℤ → ℤ × ℤ) (Ry : Finset (ℤ × ℤ)),
      (∀ I ∈ Tc, sy I ∈ Ry ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (sy I).1 (sy I).2 ∧
        ∀ L ∈ Ry, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G L.1 L.2 → L.1 ≤ (sy I).1) →
      (∀ I ∈ Tc, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (sx I).1 (sx I).2) →
      sx I = sx I' → (sy I).1 ≤ (sx I).1 → (sy I').1 ≤ (sx I').1 → sy I = sy I' := by
    intro I hI I' hI' sx sy Ry hsy hsx hxx h1 h2
    have hx := dyadicGridCell_left_mem G I.1 I.2
    have hx' := dyadicGridCell_left_mem G I'.1 I'.2
    obtain ⟨hyR, hyI, hyd⟩ := hsy I hI
    obtain ⟨hyR', hyI', hyd'⟩ := hsy I' hI'
    -- the deeper root `sx I` lies in both `sy I` and `sy I'`
    have hA : dyadicGridCell G (sx I).1 (sx I).2 ⊆ dyadicGridCell G (sy I).1 (sy I).2 :=
      dyadicGridCell_subset_of_common_point G (hsx I hI hx) (hyI hx) h1
    have hA' : dyadicGridCell G (sx I').1 (sx I').2 ⊆ dyadicGridCell G (sy I').1 (sy I').2 :=
      dyadicGridCell_subset_of_common_point G (hsx I' hI' hx') (hyI' hx') h2
    rw [← hxx] at hA'
    have e1 := hyd (sy I') hyR' ((hsx I hI).trans hA')
    have e2 := hyd' (sy I) hyR ((hsx I' hI').trans (hxx ▸ hA))
    exact dyadicGridCell_eq_of_common_point G (hA (hsx I hI hx)) (hA' (hsx I hI hx)) (by omega)
  refine add_le_add ?_ ?_
  · -- pairs where the `a` root is deeper
    have hinj : Set.InjOn (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.1)
        (P.filter (fun p => p.2.1 ≤ p.1.1) : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
      intro p hp p' hp' hpp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, P, Finset.mem_image] at hp hp'
      obtain ⟨⟨I, hI, rfl⟩, h1⟩ := hp
      obtain ⟨⟨I', hI', rfl⟩, h2⟩ := hp'
      simp only at hpp h1 h2
      exact Prod.ext hpp (key I hI I' hI' sa sb Rb hsb (fun I hI => (hsa I hI).2.1) hpp h1 h2)
    calc ∑ p ∈ P.filter (fun p => p.2.1 ≤ p.1.1), dyadicGridLength G (deeperRoot p.1 p.2).1
        = ∑ p ∈ P.filter (fun p => p.2.1 ≤ p.1.1), dyadicGridLength G p.1.1 :=
          Finset.sum_congr rfl fun p hp => by
            simp only [deeperRoot, (Finset.mem_filter.mp hp).2, ↓reduceIte]
      _ = ∑ K ∈ (P.filter (fun p => p.2.1 ≤ p.1.1)).image (fun p => p.1),
            dyadicGridLength G K.1 := (Finset.sum_image (f := fun K : ℤ × ℤ => dyadicGridLength G
                K.1) hinj).symm
      _ ≤ dyadicRootLength G Ra := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hpos c
          intro K hK
          simp only [Finset.mem_image, Finset.mem_filter, P] at hK
          obtain ⟨p, ⟨⟨I, hI, rfl⟩, -⟩, rfl⟩ := hK
          exact (hsa I hI).1
  · -- pairs where the `b` root is deeper
    have hinj : Set.InjOn (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.2)
        (P.filter (fun p => ¬ p.2.1 ≤ p.1.1) : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
      intro p hp p' hp' hpp
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, P, Finset.mem_image] at hp hp'
      obtain ⟨⟨I, hI, rfl⟩, h1⟩ := hp
      obtain ⟨⟨I', hI', rfl⟩, h2⟩ := hp'
      simp only at hpp h1 h2
      exact Prod.ext (key I hI I' hI' sb sa Ra hsa (fun I hI => (hsb I hI).2.1) hpp (by omega)
        (by omega)) hpp
    calc ∑ p ∈ P.filter (fun p => ¬ p.2.1 ≤ p.1.1), dyadicGridLength G (deeperRoot p.1 p.2).1
        = ∑ p ∈ P.filter (fun p => ¬ p.2.1 ≤ p.1.1), dyadicGridLength G p.2.1 :=
          Finset.sum_congr rfl fun p hp => by
            simp only [deeperRoot, (Finset.mem_filter.mp hp).2, ↓reduceIte]
      _ = ∑ K ∈ (P.filter (fun p => ¬ p.2.1 ≤ p.1.1)).image (fun p => p.2),
            dyadicGridLength G K.1 := (Finset.sum_image (f := fun K : ℤ × ℤ => dyadicGridLength G
                K.1) hinj).symm
      _ ≤ dyadicRootLength G Rb := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => hpos c
          intro K hK
          simp only [Finset.mem_image, Finset.mem_filter, P] at hK
          obtain ⟨p, ⟨⟨I, hI, rfl⟩, -⟩, rfl⟩ := hK
          exact (hsb I hI).1

namespace AccSetup
variable {S : AccSetup}

/-- The input has energy at most `|c|` on every tree cell. -/
theorem Hyp.input_sq_le (h : S.Hyp) {c : ℤ × ℤ} (hc : c ∈ dyadicFiniteTree S.G S.J S.N)
    (hcH : kernelHull S.G S.J S.N S.w c) :
    ∫ y in S.cell c, ‖(S.input : ℝ → ℂ) y‖ ^ 2 ≤ dyadicGridLength S.G c.1 := by
  rw [← integral_physical_sq (V := S.W)]
  exact h.energy_cell_le hc hcH

/-- The cut-off input `1_J f` has energy at most `|c|` on every tree cell. -/
theorem Hyp.indicator_sq_le (h : S.Hyp) {c : ℤ × ℤ} (hc : c ∈ dyadicFiniteTree S.G S.J S.N)
    (hcH : kernelHull S.G S.J S.N S.w c) :
    ∫ y in S.cell c, ‖(S.cell S.J).indicator S.f y‖ ^ 2 ≤ dyadicGridLength S.G c.1 := by
  refine le_of_eq_of_le (integral_congr_ae ?_) (h.input_sq_le hc hcH)
  filter_upwards [ae_restrict_of_ae h.input_ae] with y hy
  rw [hy]

end AccSetup

theorem sqrt_mul_sqrt_le_of_le {x y r : ℝ} (hx : x ≤ r) (hy : y ≤ r) (hr : 0 ≤ r) :
    Real.sqrt x * Real.sqrt y ≤ r := by
  calc Real.sqrt x * Real.sqrt y ≤ Real.sqrt r * Real.sqrt r :=
        mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = r := Real.mul_self_sqrt hr

section BaseSegments

theorem arith_two_terms {c Ea Eb X Y s1 s2 s3 s4 r : ℝ} (hc : 0 ≤ c) (hEa : 0 ≤ Ea)
    (hEb : 0 ≤ Eb) (hX : 0 ≤ X) (hY : 0 ≤ Y) (h1 : s1 * s2 ≤ r) (h2 : s3 * s4 ≤ r) :
    c * (Ea * X) * s1 * s2 + c * (Eb * Y) * s3 * s4 ≤ c * (Ea * X + Eb * Y) * r := by
  have k1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc (mul_nonneg hEa hX))
  have k2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hc (mul_nonneg hEb hY))
  calc c * (Ea * X) * s1 * s2 + c * (Eb * Y) * s3 * s4 =
      c * (Ea * X) * (s1 * s2) + c * (Eb * Y) * (s3 * s4) := by ring
    _ ≤ c * (Ea * X) * r + c * (Eb * Y) * r := add_le_add k1 k2
    _ = _ := by ring

variable (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {c₀ c₁ : ℕ} {H : ℝ}
  (Xi Xk : LowList G J N J c₀ H) {a i k b : Fin 4} (Bp D : ℝ)
  (pkga : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) a i k b Bp D c₁)
  (pkgb : ∀ (K K' : ℤ × ℤ) (li : Xi.Λ) (lk : Xk.Λ),
    PredictorPackage κ (Xi.chart K li) (Xk.chart K' lk) b i k a Bp D c₁)
  {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)

/-- Blueprint prop:base (one first-level root `J`): the cells `T_c` of the coarse tree are
partitioned by their pairs of accurate-fit segments; on each pair, rooted at the deeper of the
two segment roots, `baseRoot` gives an active setup. The roots have total length at most
`8/3 |J|`. -/
theorem baseSegments (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b)
    (hkb : k ≠ b) (hD1 : 1 ≤ D) (K₀ Ma Mb : ℕ) (f : Fin 4 → ℝ → ℂ) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (q : ℝ) (ka kb c₂ : ℕ) (Ba Bb : ℝ)
    (hSa : (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).Hyp)
    (hSb : (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).Hyp)
    (hw : ∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
      (w I))
    (Xga Xgb : LowList G J N J c₀ H) (zga zgb : ℤ × ℤ → ℝ → ℂ) {Cga Cgb : ℝ} (hCga : 0 ≤ Cga)
    (hCgb : 0 ≤ Cgb)
    (hzga : (∀ I, Measurable (zga I) ∧ MemLp (zga I) 2 (volume.restrict (dyadicGridCell G I.1
        I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N,
        IsAdmissibleOpponent G J' (f a) zga Cga ∧ HasDepthEnergy G J' (f a) zga 1)
    (hzgb : (∀ I, Measurable (zgb I) ∧ MemLp (zgb I) 2 (volume.restrict (dyadicGridCell G I.1
        I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N,
        IsAdmissibleOpponent G J' (f b) zgb Cgb ∧ HasDepthEnergy G J' (f b) zgb 1)
    (Tc : Finset (ℤ × ℤ))
    (hTc : ∀ I ∈ Tc, I ∈ dyadicFiniteTree G J
        (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).Nc ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zga I y = Xga.val I y) ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y))
    (hTcH : ∀ I ∈ Tc, kernelHull G J N w I)
    (hq : 2 ≤ q) (hfm : ∀ l, Measurable (f l))
    (hfq : ∀ I ∈ Tc, ∀ l, eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1)
    (hLi : ∀ I ∈ Tc, eLpNorm (Xi.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2)
    (hLk : ∀ I ∈ Tc, eLpNorm (Xk.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2)
    (hLga : ∀ I ∈ Tc, eLpNorm (Xga.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1)
    (hLgb : ∀ I ∈ Tc, eLpNorm (Xgb.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1)
    {η₀ δa δb : ℝ} (hη₀ : 0 ≤ η₀) (hδa : 0 ≤ δa) (hδb : 0 ≤ δb)
    (hpairs : ∀ I ∈ Tc, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s'
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s)
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s') η₀)
    (hsa : ∀ I ∈ Tc, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) a q
      (f a - (predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).phys I
        ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.st I).1
        ((predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba).tree.st I).2)
      δa)
    (hsb : ∀ I ∈ Tc, FormSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) b q
      (f b - (predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).phys I
        ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.st I).1
        ((predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb).tree.st I).2)
      δb)
    {c' : ℕ} {H' : ℝ} (hc₀ : c₀ ≤ c') (hc₁ : c₁ ≤ c') (hc₂ : c₂ ≤ c') (hHH : H ≤ H')
    (hDH : D ≤ H') (hBa : Ba ≤ H') (hBb : Bb ≤ H')
    (hdef₀ : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ)
    {Bd : ℝ} {cB : ℕ} {HB : ℝ}
    (hri : ∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧ IsBasicOn G J N 1 Bd cB HB w z₂ ∧
      ∀ I ∈ Tc, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (hrk : ∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧ IsBasicOn G J N 1 Bd cB HB w z₂ ∧
      ∀ I ∈ Tc, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (hrga : IsBasicOn G J N 1 Bd cB HB w zga) (hrgb : IsBasicOn G J N 1 Bd cB HB w zgb)
    (hBd : Bd ≤ 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ : ℕ) : ℝ)) (hcB : cB ≤ c') (hHB : HB ≤ H') :
    let Sa := predAccSetup κ Xi Xk a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂ Ba
    let Sb := predAccSetup κ Xi Xk b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂ Bb
    let Ea := 2 * Real.exp (-Bp) * (2 * (compressionOneConst ((Sa.system J).rooted J) + K₀) + 1)
      + D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)
    let Eb := 2 * Real.exp (-Bp) * (2 * (compressionOneConst ((Sb.system J).rooted J) + K₀) + 1)
      + D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)
    let E := (Fintype.card Xi.Λ * Fintype.card Xk.Λ) * (Ea * (2 * (1 + Cgb) + 4) +
      Eb * (2 * (2 * (compressionOneConst ((Sa.system J).rooted J) + K₀) + Cga) + 4))
    let S₀ : ℝ := 1 + Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ
    let Sp : ℝ := Fintype.card Sa.W * Real.sqrt (2 ^ K₀ / ε) + 1
    ∃ (P : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (A : P → ActiveSetup κ c'),
      ∑ p : P, dyadicGridLength G (A p).R.1 ≤ 8 / 3 * dyadicGridLength G J.1 ∧
      (∀ I ∈ Tc, ∃ p : P, I ∈ (A p).cells) ∧
      (∀ p p' : P, ∀ I, I ∈ (A p).cells → I ∈ (A p').cells → p = p') ∧
      ∀ p : P, (A p).cells ⊆ Tc ∧
        (∀ I ∈ (A p).cells, ∀ J' ∈ Tc, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 →
          dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A p).cells) ∧
        (A p).G = G ∧ (A p).w = w ∧ (A p).a = a ∧ (A p).b = b ∧
        (A p).R ∈ dyadicFiniteTree G J N ∧
        (A p).H = H' ∧ (A p).Dc = Real.sqrt ε⁻¹ ∧ (A p).S = 2 ∧ (A p).η = 4 * η₀ ∧
        Fintype.card (A p).L = Fintype.card Xi.Λ + Fintype.card Xk.Λ +
          (Fintype.card Sa.W + Fintype.card Xga.Λ) + (Fintype.card Sb.W + Fintype.card Xgb.Λ) ∧
        ∑ I ∈ (A p).cells, dyadicGridLength G I.1 *
          ‖localProgressionForm (dyadicGridLength G I.1) (w I)
              (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I)) -
            (A p).Hf I ((A p).Y I)‖ ≤ E * dyadicGridLength G (A p).R.1 ∧
        (∀ I ∈ (A p).cells, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
          (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A p).Y I s')
          (η₀ + (2 + 2 * S₀) * (δa + δb) + (1 + Sp) * δb)) ∧
        (∀ I ∈ (A p).cells, ∀ l, (eLpNorm ((A p).Y I l) 2 ((A p).μ I)).toReal ≤ 2) ∧
        (∀ l, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 *
          (eLpNorm ((A p).U l I) 2 ((A p).μ I)).toReal ^ 2 ≤
            (K₀ : ℝ) ^ 2 * dyadicGridLength G (A p).R.1) ∧
        ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).z 3 I)‖ ≤
          η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G (A p).R.1) ∧
        (A p).HasColumnRep 1 ∧ (A p).SubRootProps η₀ ((K₀ : ℝ) ^ 2) := by
  intro Sa Sb Ea Eb E S₀ Sp
  classical
  have hthA := hSa.treeHyp
  have hthB := hSb.treeHyp
  have hspecA : ∀ I ∈ Tc, Sa.tree.seg I ∈ Sa.tree.roots ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Sa.tree.seg I).1 (Sa.tree.seg I).2 ∧
      ∀ L ∈ Sa.tree.roots, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G L.1 L.2 →
        L.1 ≤ (Sa.tree.seg I).1 := fun I hI => by
    obtain ⟨h1, h2, -, h4⟩ := hthA.seg_spec (hTc I hI).1
    exact ⟨h1, h2, h4⟩
  have hspecB : ∀ I ∈ Tc, Sb.tree.seg I ∈ Sb.tree.roots ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Sb.tree.seg I).1 (Sb.tree.seg I).2 ∧
      ∀ L ∈ Sb.tree.roots, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G L.1 L.2 →
        L.1 ≤ (Sb.tree.seg I).1 := fun I hI => by
    obtain ⟨h1, h2, -, h4⟩ := hthB.seg_spec (hTc I hI).1
    exact ⟨h1, h2, h4⟩
  set! P := Tc.image (fun I => (Sa.tree.seg I, Sb.tree.seg I)) with hP_def
  have hPmem : ∀ p ∈ P, ∃ I ∈ Tc, (Sa.tree.seg I, Sb.tree.seg I) = p := fun p hp => by
    simpa [hP_def] using hp
  set! T : P → Finset (ℤ × ℤ) := fun p => Tc.filter (fun I => (Sa.tree.seg I, Sb.tree.seg I) = p.1)
    with hT_def
  have hTmem : ∀ p : P, ∀ I ∈ T p, I ∈ Tc ∧ Sa.tree.seg I = p.1.1 ∧ Sb.tree.seg I = p.1.2 :=
    fun p I hI => by
      obtain ⟨hI1, hI2⟩ := Finset.mem_filter.mp hI
      exact ⟨hI1, by rw [← hI2], by rw [← hI2]⟩
  have hroot : ∀ p : P, p.1.1 ∈ Sa.tree.roots ∧ p.1.2 ∈ Sb.tree.roots := fun p => by
    obtain ⟨I, hI, he⟩ := hPmem p.1 p.2
    rw [← he]
    exact ⟨(hspecA I hI).1, (hspecB I hI).1⟩
  have hRtree : ∀ p : P, deeperRoot p.1.1 p.1.2 ∈ dyadicFiniteTree G J N := fun p => by
    unfold deeperRoot; split_ifs
    · exact AccSetup.coarse_tree hSa (hthA.roots_mem (hroot p).1)
    · exact AccSetup.coarse_tree hSb (hthB.roots_mem (hroot p).2)
  have hRH : ∀ p : P, kernelHull G J N w (deeperRoot p.1.1 p.1.2) := fun p => by
    obtain ⟨I, hI, he⟩ := hPmem p.1 p.2
    have h1 := (hspecA I hI).2.1
    have h2 := (hspecB I hI).2.1
    have hIa : Sa.tree.seg I = p.1.1 := by rw [← he]
    have hIb : Sb.tree.seg I = p.1.2 := by rw [← he]
    rw [hIa] at h1
    rw [hIb] at h2
    exact (hTcH I hI).mono (cell_subset_deeperRoot G h1 h2)
  have hex := fun p : P => baseRoot κ Xi Xk Bp D pkga pkgb hε0 hε1 hai hak hab hik hib hkb hD1
    K₀ Ma Mb f w q ka kb c₂ Ba Bb hSa hSb hw (hroot p).1 (hroot p).2 (hRtree p) Xga Xgb zga zgb
    hCga hCgb ⟨hzga.1, fun J' hJ' _ => hzga.2 J' hJ'⟩ ⟨hzgb.1, fun J' hJ' _ => hzgb.2 J' hJ'⟩
    (T p) (fun I hI => by
      obtain ⟨hI1, hIa, hIb⟩ := hTmem p I hI
      refine ⟨(hTc I hI1).1, hIa, hIb, ?_, (hTc I hI1).2.1, (hTc I hI1).2.2⟩
      have h1 := (hspecA I hI1).2.1
      have h2 := (hspecB I hI1).2.1
      rw [hIa] at h1
      rw [hIb] at h2
      exact cell_subset_deeperRoot G h1 h2)
    (fun I hI => hTcH I (hTmem p I hI).1) (hRH p)
    hq hfm (fun I hI => hfq I (hTmem p I hI).1) (fun I hI => hLi I (hTmem p I hI).1)
    (fun I hI => hLk I (hTmem p I hI).1) (fun I hI => hLga I (hTmem p I hI).1)
    (fun I hI => hLgb I (hTmem p I hI).1) hη₀ hδa hδb
    (fun I hI => hpairs I (hTmem p I hI).1) (fun I hI => hsa I (hTmem p I hI).1)
    (fun I hI => hsb I (hTmem p I hI).1) hc₀ hc₁ hc₂ hHH hDH hBa hBb hdef₀
    (by
      obtain ⟨z₁, z₂, h₁, h₂, h₃⟩ := hri
      exact ⟨z₁, z₂, h₁, h₂, fun I hI => h₃ I (hTmem p I hI).1⟩)
    (by
      obtain ⟨z₁, z₂, h₁, h₂, h₃⟩ := hrk
      exact ⟨z₁, z₂, h₁, h₂, fun I hI => h₃ I (hTmem p I hI).1⟩)
    hrga hrgb hBd hcB hHB
  dsimp only at hex
  choose A hA using hex
  refine ⟨P, A, ?_, ?_, ?_, fun p => ?_⟩
  · -- packing
    have hRl : ∀ p : P, (A p).R = deeperRoot p.1.1 p.1.2 := fun p => (hA p).2.1
    calc ∑ p : P, dyadicGridLength G (A p).R.1
        = ∑ p : P, dyadicGridLength G (deeperRoot p.1.1 p.1.2).1 :=
          Finset.sum_congr rfl fun p _ => by rw [hRl p]
      _ = ∑ p ∈ P, dyadicGridLength G (deeperRoot p.1 p.2).1 :=
          Finset.sum_coe_sort P (fun p => dyadicGridLength G (deeperRoot p.1 p.2).1)
      _ ≤ dyadicRootLength G Sa.tree.roots + dyadicRootLength G Sb.tree.roots :=
          sum_deeperRoot_le G Tc Sa.tree.roots Sb.tree.roots Sa.tree.seg Sb.tree.seg hspecA hspecB
      _ ≤ 4 / 3 * dyadicGridLength G J.1 + 4 / 3 * dyadicGridLength G J.1 :=
          add_le_add hthA.roots_length_le hthB.roots_length_le
      _ = 8 / 3 * dyadicGridLength G J.1 := by ring
  · -- covering
    intro I hI
    refine ⟨⟨(Sa.tree.seg I, Sb.tree.seg I), Finset.mem_image_of_mem _ hI⟩, ?_⟩
    rw [(hA _).2.2.1]
    exact Finset.mem_filter.mpr ⟨hI, rfl⟩
  · -- disjointness
    intro p p' I hp hp'
    rw [(hA p).2.2.1] at hp
    rw [(hA p').2.2.1] at hp'
    exact Subtype.ext ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hp').2)
  · obtain ⟨hG, hR, hcells, hw', ha, hb, hH, hDc, hS, hη, hcard, hrep, hpair, hsize, hside,
      htwo, hcol, hsr⟩ := hA p
    rw [← hR] at hside htwo hrep
    have hclos : ∀ I ∈ T p, ∀ J' ∈ Tc, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 →
        dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ T p := by
      intro I hI J' hJ' hIJ hJR
      obtain ⟨hI1, hIa, hIb⟩ := hTmem p I hI
      rw [hR] at hJR
      have hsa := (hspecA I hI1).2.1
      have hsb := (hspecB I hI1).2.1
      obtain ⟨hda, hdb⟩ := deeperRoot_subset G hsa hsb
      rw [hIa, hIb] at hda hdb
      have e1 : Sa.tree.seg J' = Sa.tree.seg I := hthA.seg_between (hTc I hI1).1 (hTc J' hJ').1
        hIJ (by rw [hIa]; exact hJR.trans hda)
      have e2 : Sb.tree.seg J' = Sb.tree.seg I := hthB.seg_between (hTc I hI1).1 (hTc J' hJ').1
        hIJ (by rw [hIb]; exact hJR.trans hdb)
      refine Finset.mem_filter.mpr ⟨hJ', ?_⟩
      rw [e1, e2, hIa, hIb]
    rw [hcells]
    refine ⟨Finset.filter_subset _ _, fun I hI J' hJ' hIJ hJR => by
      rw [← hcells] at hI ⊢; exact hcells ▸ hclos I (hcells ▸ hI) J' hJ' hIJ hJR, hG, hw', ha,
      hb, by rw [hR]; exact hRtree p, hH, hDc, hS, hη, hcard, ?_, hpair, hsize, hside, htwo, hcol,
      hsr⟩
    refine hrep.trans ?_
    have hRR := hRtree p
    have hRRH := hRH p
    have hRa : ∫ y in dyadicGridCell G (A p).R.1 (A p).R.2, ‖(Sa.input : ℝ → ℂ) y‖ ^ 2 ≤
        dyadicGridLength G (A p).R.1 := by rw [hR]; exact hSa.input_sq_le hRR hRRH
    have hRb : ∫ y in dyadicGridCell G (A p).R.1 (A p).R.2, ‖(Sb.input : ℝ → ℂ) y‖ ^ 2 ≤
        dyadicGridLength G (A p).R.1 := by rw [hR]; exact hSb.input_sq_le hRR hRRH
    have hFa : ∫ y in dyadicGridCell G (A p).R.1 (A p).R.2,
        ‖(dyadicGridCell G J.1 J.2).indicator (f a) y‖ ^ 2 ≤ dyadicGridLength G (A p).R.1 := by
      rw [hR]; exact hSa.indicator_sq_le hRR hRRH
    have hFb : ∫ y in dyadicGridCell G (A p).R.1 (A p).R.2,
        ‖(dyadicGridCell G J.1 J.2).indicator (f b) y‖ ^ 2 ≤ dyadicGridLength G (A p).R.1 := by
      rw [hR]; exact hSb.indicator_sq_le hRR hRRH
    have hr0 := (dyadicGridLength_pos G (A p).R.1).le
    have h1 := sqrt_mul_sqrt_le_of_le hRa hFb hr0
    have h2 := sqrt_mul_sqrt_le_of_le hRb hFa hr0
    have hca : compressionOneConst ((Sa.system p.1.1).rooted (A p).R) =
        compressionOneConst ((Sa.system J).rooted J) := rfl
    have hcb : compressionOneConst ((Sb.system p.1.2).rooted (A p).R) =
        compressionOneConst ((Sb.system J).rooted J) := rfl
    rw [hca, hcb] at hrep ⊢
    have hcomp : ∀ (V : Type) [Fintype V] (D' : ColumnTreeData V), 0 ≤ compressionOneConst D' := by
      intro V _ D'
      unfold compressionOneConst
      exact pow_nonneg (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith only [D'.two_le_budget]))) _
    have hxa := hcomp _ ((Sa.system J).rooted J)
    have hxb := hcomp _ ((Sb.system J).rooted J)
    have hdel := delayConst_nonneg κ
    have hD0 : (0 : ℝ) ≤ 1 + D := by linarith
    have hε' : 0 ≤ (2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε :=
      add_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    have hK : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
    have hEa : 0 ≤ Ea := add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos _).le)
      (by linarith)) (mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hdel hε')
        (pow_nonneg hD0 _)))
    have hEb : 0 ≤ Eb := add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos _).le)
      (by linarith)) (mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hdel hε')
        (pow_nonneg hD0 _)))
    have hX : 0 ≤ 2 * (1 + Cgb) + 4 := by linarith
    have hY : 0 ≤ 2 * (2 * (compressionOneConst ((Sa.system J).rooted J) + K₀) + Cga) + 4 := by
      linarith
    have hc1 : (0 : ℝ) ≤ Fintype.card Xi.Λ * Fintype.card Xk.Λ := by positivity
    exact arith_two_terms hc1 hEa hEb hX hY h1 h2

end BaseSegments

/-! ### The low lists of the stagger fits on a tree cell -/

/-- Blueprint prop:base, proof lines 1626-1630: an adaptive fit with its attempt data gives, on a
tree cell `R`, a low list of padded charts agreeing with the fit on the cells of the segment of
`R` below `R`, with coefficients of modulus at most one and normalized `L²` size at most one. -/
theorem fitLowList_exists :
    ∃ (cp : ℕ) (Wp : ℝ), 1 ≤ cp ∧ Real.exp 2 ≤ Wp ∧
    (∀ (c : ℕ) (H' : ℝ), cp ≤ c → Wp ≤ H' → ∃ (d : ℕ) (Φ : QuadraticChartData d), 1 ≤ d ∧
      QuadraticChartComplexity c H' Φ ∧ IsBoundedQuadraticChart Φ) ∧
    ∀ {c₂ : ℕ} {B : ℝ} {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ}
      {w : ℤ × ℤ → ℝ × ℝ → ℂ} {j : Fin 4} {q : ℝ} {f : ℝ → ℂ} {k : ℕ} {M : ℕ}
      {roots : Finset (ℤ × ℤ)} {seg : ℤ × ℤ → ℤ × ℤ} {n : ℤ × ℤ → ℕ}
      {a : ℤ × ℤ → ℕ → ℝ → ℂ} {g : ℤ × ℤ → ℝ → ℂ} {cnt : ℤ × ℤ → ℤ × ℤ → ℕ}
      {atm : ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ},
      1 ≤ c₂ → IsAdaptiveFit c₂ B G J N w j q f k M roots seg n a g →
      IsAttemptData c₂ B G J N M roots seg n a cnt atm →
      ∀ {R : ℤ × ℤ}, R ∈ dyadicFiniteTree G J N →
      ∃ X : LowList G J N R (max c₂ cp) (max B Wp ^ 6), Fintype.card X.Λ = M ∧
        ∀ I ∈ dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 →
          seg I = seg R → kernelHull G J N w I → ∀ y, X.val I y = g I y := by
  obtain ⟨cp, Wp, hcp, hWp, hpadc⟩ := exists_pad_chart
  obtain ⟨cu, Wu, E, hcu, hWu, hE1, hEc⟩ := exists_unit_chart
  refine ⟨max cp cu, max Wp Wu, le_trans hcp (le_max_left _ _), le_trans hWp (le_max_left _ _),
    fun c H' hc hH' => ⟨1, E, le_rfl, quadraticChartComplexity_order_mono
      (hEc H' (le_trans (le_max_right _ _) hH')) (le_trans (le_max_right _ _) hc),
      fun y => by rw [hE1]; simp⟩, ?_⟩
  intro c₂ B G J N w j q f k M roots seg n a g cnt atm hc₂ hF hA R hR
  obtain ⟨hKr, hRK, -⟩ := hF.2.2.2.2 R hR
  have hWle : max B Wp ^ 6 ≤ max B (max Wp Wu) ^ 6 := by
    have : 0 ≤ max B Wp := le_trans (by positivity) (le_max_right B Wp |>.trans' hWp)
    exact pow_le_pow_left₀ this (max_le_max le_rfl (le_max_left _ _)) 6
  have hge : Wu ≤ max B (max Wp Wu) ^ 6 := by
    have h1 : Wu ≤ max B (max Wp Wu) := le_trans (le_max_right Wp Wu) (le_max_right _ _)
    have h2 : 1 ≤ max B (max Wp Wu) :=
      le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) (hWu.trans h1)
    calc Wu ≤ max B (max Wp Wu) := h1
      _ = max B (max Wp Wu) ^ 1 := (pow_one _).symm
      _ ≤ max B (max Wp Wu) ^ 6 := pow_le_pow_right₀ h2 (by norm_num)
  have hpad : ∀ (b : ℤ × ℤ) (m : Fin M), b ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G b.1 b.2 ⊆ dyadicGridCell G (seg R).1 (seg R).2 ∧ (m : ℕ) < cnt (seg R) b →
      ∃ (d : ℕ) (Φ : QuadraticChartData d), 1 ≤ d ∧
        QuadraticChartComplexity (max c₂ (max cp cu)) (max B (max Wp Wu) ^ 6) Φ ∧
        IsBoundedQuadraticChart Φ ∧ ∀ y, quadraticChartAtom Φ y = atm (seg R) b m y := by
    rintro b m ⟨hb, hbK, hm⟩
    obtain ⟨-, hch⟩ := hA.2.2 (seg R) hKr b hb hbK
    obtain ⟨d, Φ, hΦc, hΦb, hΦe⟩ := hch m hm
    obtain ⟨Φ', hΦ'a, hΦ'c, hΦ'b⟩ := hpadc Φ hΦc hc₂
    refine ⟨d + 1, Φ', by omega, ?_, hΦ'b hΦb, fun y => by rw [hΦ'a, hΦe]⟩
    exact quadraticChartComplexity_order_mono (quadraticChartComplexity_mono hΦ'c hWle)
      (max_le_max le_rfl (le_max_left _ _))
  have hdef : ∃ (d : ℕ) (Φ : QuadraticChartData d), 1 ≤ d ∧
      QuadraticChartComplexity (max c₂ (max cp cu)) (max B (max Wp Wu) ^ 6) Φ ∧
      IsBoundedQuadraticChart Φ :=
    ⟨1, E, le_rfl, quadraticChartComplexity_order_mono (hEc _ hge)
      (le_trans (le_max_right cp cu) (le_max_right _ _)), fun y => by rw [hE1]; simp⟩
  refine ⟨fitLowList hF hA hR hKr hRK hpad hdef, Fintype.card_fin M,
    fun I hI hIR hseg hIH y => fitLowList_val hF hA hR hKr hRK hpad hdef hI hIR hseg hIH y⟩

section FirstRoot
variable (seg : ℕ → ℤ × ℤ → ℤ × ℤ) (L : Finset ℕ) (hL : L.Nonempty)

/-! ### First-level roots: the common refinement of finitely many segment families -/

/-- The deepest of the segment roots of a cell over the levels in `L`. -/
noncomputable def firstRoot (I : ℤ × ℤ) : ℤ × ℤ :=
  seg (Classical.choose (L.exists_max_image (fun ℓ => (seg ℓ I).1) hL)) I

theorem firstRoot_spec (I : ℤ × ℤ) :
    (∃ ℓ ∈ L, firstRoot seg L hL I = seg ℓ I) ∧
      ∀ ℓ ∈ L, (seg ℓ I).1 ≤ (firstRoot seg L hL I).1 := by
  have h := Classical.choose_spec (L.exists_max_image (fun ℓ => (seg ℓ I).1) hL)
  exact ⟨⟨_, h.1, rfl⟩, h.2⟩

variable {seg L hL} {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ}

/-- Segment data: each segment root contains the cell, lies in the tree, and the segment is
constant between a cell and its segment root. -/
def SegData (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (seg : ℕ → ℤ × ℤ → ℤ × ℤ) (L : Finset ℕ) :
    Prop :=
  ∀ ℓ ∈ L, ∀ I ∈ dyadicFiniteTree G J N,
    dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (seg ℓ I).1 (seg ℓ I).2 ∧
    seg ℓ I ∈ dyadicFiniteTree G J N ∧
    ∀ I' ∈ dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 →
      dyadicGridCell G I'.1 I'.2 ⊆ dyadicGridCell G (seg ℓ I).1 (seg ℓ I).2 → seg ℓ I' = seg ℓ I

theorem firstRoot_mem (h : SegData G J N seg L) {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree G J N) :
    firstRoot seg L hL I ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G I.1 I.2 ⊆
        dyadicGridCell G (firstRoot seg L hL I).1 (firstRoot seg L hL I).2 := by
  obtain ⟨⟨ℓ, hℓ, he⟩, -⟩ := firstRoot_spec seg L hL I
  rw [he]
  exact ⟨(h ℓ hℓ I hI).2.1, (h ℓ hℓ I hI).1⟩

/-- A cell between a tree cell and its first-level root has the same first-level root. -/
theorem firstRoot_between (h : SegData G J N seg L) {I I' : ℤ × ℤ}
    (hI : I ∈ dyadicFiniteTree G J N) (hI' : I' ∈ dyadicFiniteTree G J N)
    (hII' : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2)
    (hI'R : dyadicGridCell G I'.1 I'.2 ⊆
      dyadicGridCell G (firstRoot seg L hL I).1 (firstRoot seg L hL I).2) :
    firstRoot seg L hL I' = firstRoot seg L hL I := by
  have hx := dyadicGridCell_left_mem G I.1 I.2
  obtain ⟨hRT, hIR⟩ := firstRoot_mem (hL := hL) h hI
  have hsame : ∀ ℓ ∈ L, seg ℓ I' = seg ℓ I := fun ℓ hℓ => by
    have hRs : dyadicGridCell G (firstRoot seg L hL I).1 (firstRoot seg L hL I).2 ⊆
        dyadicGridCell G (seg ℓ I).1 (seg ℓ I).2 :=
      dyadicGridCell_subset_of_common_point G (hIR hx) ((h ℓ hℓ I hI).1 hx)
        ((firstRoot_spec seg L hL I).2 ℓ hℓ)
    exact (h ℓ hℓ I hI).2.2 I' hI' hII' (hI'R.trans hRs)
  obtain ⟨⟨ℓ₁, hℓ₁, e₁⟩, hmax₁⟩ := firstRoot_spec seg L hL I'
  obtain ⟨⟨ℓ₂, hℓ₂, e₂⟩, hmax₂⟩ := firstRoot_spec seg L hL I
  rw [hsame ℓ₁ hℓ₁] at e₁
  have d1 := hmax₁ ℓ₂ hℓ₂
  rw [hsame ℓ₂ hℓ₂, e₁] at d1
  have d2 := hmax₂ ℓ₁ hℓ₁
  rw [e₂] at d2
  rw [e₁, e₂]
  exact dyadicGridCell_eq_of_common_point G ((h ℓ₁ hℓ₁ I hI).1 hx) ((h ℓ₂ hℓ₂ I hI).1 hx)
    (by omega)

/-- The segments of a cell are those of its first-level root. -/
theorem seg_firstRoot (h : SegData G J N seg L) {I : ℤ × ℤ} (hI : I ∈ dyadicFiniteTree G J N)
    {ℓ : ℕ} (hℓ : ℓ ∈ L) : seg ℓ (firstRoot seg L hL I) = seg ℓ I := by
  obtain ⟨hRT, hIR⟩ := firstRoot_mem (hL := hL) h hI
  have hx := dyadicGridCell_left_mem G I.1 I.2
  have hRs : dyadicGridCell G (firstRoot seg L hL I).1 (firstRoot seg L hL I).2 ⊆
      dyadicGridCell G (seg ℓ I).1 (seg ℓ I).2 :=
    dyadicGridCell_subset_of_common_point G (hIR hx) ((h ℓ hℓ I hI).1 hx)
      ((firstRoot_spec seg L hL I).2 ℓ hℓ)
  exact (h ℓ hℓ I hI).2.2 _ hRT hIR hRs

/-- First-level roots are roots of one of the levels; hence their total length is at most that
of the union of the root families. -/
theorem sum_firstRoot_le (roots : ℕ → Finset (ℤ × ℤ))
    (hroots : ∀ ℓ ∈ L, ∀ I ∈ dyadicFiniteTree G J N, seg ℓ I ∈ roots ℓ)
    (T : Finset (ℤ × ℤ)) (hT : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N) :
    ∑ R ∈ T.image (firstRoot seg L hL), dyadicGridLength G R.1 ≤
      dyadicRootLength G (L.biUnion roots) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ => (dyadicGridLength_pos G c.1).le
  intro R hR
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨⟨ℓ, hℓ, he⟩, -⟩ := firstRoot_spec seg L hL I
  rw [he]
  exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hroots ℓ hℓ I (hT I hI)⟩

end FirstRoot

/-! ### Helpers for the first-level roots -/

theorem eLpNorm_two_le_of_q {a r : ℝ} (hr : 0 < r) {g : ℝ → ℂ} {q : ℝ}
    (hq : 2 ≤ q) (h : eLpNorm g (ENNReal.ofReal q) (normalizedIntervalMeasure a r) ≤ 1) :
    eLpNorm g 2 (normalizedIntervalMeasure a r) ≤ 1 := by
  have := normalizedIntervalMeasure_probability a hr
  refine le_trans (eLpNorm_le_eLpNorm_of_exponent_le ?_) h
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
  exact ENNReal.ofReal_le_ofReal hq

/-- The energy of the cut-off input on a cell normalized in `L²`. -/
theorem cell_indicator_sq_le {G : RealDyadicGrid} {J c : ℤ × ℤ} {f : ℝ → ℂ}
    (hcJ : dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G J.1 J.2)
    (hn : eLpNorm f 2 (normalizedIntervalMeasure (dyadicGridLeft G c.1 c.2)
      (dyadicGridLength G c.1)) ≤ 1) :
    ∫ y in dyadicGridCell G c.1 c.2, ‖(dyadicGridCell G J.1 J.2).indicator f y‖ ^ 2 ≤
      1 * dyadicGridLength G c.1 := by
  have hr := dyadicGridLength_pos G c.1
  have heq : ∫ y in dyadicGridCell G c.1 c.2, ‖(dyadicGridCell G J.1 J.2).indicator f y‖ ^ 2 =
      ∫ y in dyadicGridCell G c.1 c.2, ‖f y‖ ^ 2 :=
    setIntegral_congr_fun (dyadicGridCell_measurable _ _ _) fun y hy => by
      simp only [Set.indicator_of_mem (hcJ hy)]
  rw [← ENNReal.ofReal_one] at hn
  have hsq := sqrt_normalized_le_of_eLpNorm hr zero_le_one hn
  rw [Real.sqrt_le_iff] at hsq
  have h2 := hsq.2
  rw [one_pow, inv_mul_le_iff₀ hr, mul_one] at h2
  rw [heq, one_mul]
  exact h2

theorem ColumnDepthFamily.currentZ_zero_ae {V : Type*} [Fintype V] (Ψ : ColumnDepthFamily V)
    (I : ℤ × ℤ) : ∀ᵐ y ∂volume, Ψ.currentZ 0 I y = 0 := by
  classical
  unfold ColumnDepthFamily.currentZ
  split_ifs with h
  · rw [map_zero]
    filter_upwards [Lp.coeFn_zero (ColumnHilbert V) 2 (volume : Measure ℝ)] with y hy
    rw [hy]; rfl
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- A basic family has a basic zero family on the same columns. -/
theorem IsBasicOn.zero {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {CF Bd : ℝ} {c : ℕ} {Hc : ℝ}
    (hCF : 0 ≤ CF) {w : ℤ × ℤ → ℝ × ℝ → ℂ} {z : ℤ × ℤ → ℝ → ℂ}
    (h : IsBasicOn G J N CF Bd c Hc w z) :
    ∃ z₀, IsBasicOn G J N CF Bd c Hc w z₀ ∧ ∀ I, ∀ᵐ y ∂volume, z₀ I y = 0 := by
  obtain ⟨V, _, Ψ, Z, hG, hJ, hb, hch, -, -⟩ := h
  refine ⟨fun I => Ψ.currentZ 0 I, ⟨V, inferInstance, Ψ, 0, hG, hJ, hb, hch, fun R _ _ => ?_,
    fun I => rfl⟩, fun I => Ψ.currentZ_zero_ae I⟩
  have : ∫ y in dyadicGridCell G R.1 R.2, ‖((0 : ColumnL2 V) : ℝ → ColumnHilbert V) y‖ ^ 2 = 0 :=
    integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => by simp)
  rw [this]
  exact mul_nonneg hCF (dyadicGridLength_pos G R.1).le

/-- The fit opponent of the segment root above a tree cell `R`, as a basic family below `R`. -/
theorem isBasicOn_of_current {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {f : ℝ → ℂ}
    {w : ℤ × ℤ → ℝ × ℝ → ℂ}
    {q : ℝ} (hq : 2 ≤ q) (hfq : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I →
      eLpNorm f (ENNReal.ofReal q)
        (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1)
    {K R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N)
    (hRK : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G K.1 K.2) {z : ℤ × ℤ → ℝ → ℂ} {Bd : ℝ}
    {c : ℕ} {Hc : ℝ}
    (hz : ∃ (V : Type) (_ : Fintype V) (Ψ : ColumnDepthFamily V)
      (F : Lp ℂ 2 (volume : Measure ℝ)), Ψ.D.grid = G ∧ Ψ.D.root = K ∧ Ψ.D.budget ≤ Bd ∧
        (∀ c' ∈ dyadicFiniteTree G J N, dyadicGridCell G c'.1 c'.2 ⊆ dyadicGridCell G K.1 K.2 →
          c' ∈ Ψ.D.cells ∧ c'.1 ≤ Ψ.N ∧ ∀ v ∈ Ψ.A.labels c', ∃ (d : ℕ) (Φ : QuadraticChartData d),
            QuadraticChartComplexity c Hc Φ ∧ IsBoundedQuadraticChart Φ ∧
            ∀ y ∈ dyadicGridCell G c'.1 c'.2, Ψ.D.scalar v y = quadraticChartAtom Φ y) ∧
        (∀ I, z I = Ψ.current F I) ∧
        (F : ℝ → ℂ) =ᵐ[volume] (dyadicGridCell G J.1 J.2).indicator f) :
    IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c Hc w z := by
  obtain ⟨V, _, Ψ, F, hG, hroot, hb, hch, hzΨ, hF⟩ := hz
  refine ⟨V, inferInstance, Ψ, physicalColumnInput F, hG, by rw [hroot]; exact hRK, hb,
    fun c' hc' => ?_, fun R' hR' hR'H => ?_, hzΨ⟩
  · have hb' := (dyadicFiniteTree_below_iff G J N hR c').mp hc'
    exact hch c' hb'.1 (hb'.2.trans hRK)
  have hR'J := ((dyadicFiniteTree_below_iff G J N hR R').mp hR').1
  have hR'H' := (kernelHull_below_iff hR ((dyadicFiniteTree_below_iff G J N hR R').mp hR').2).mp
    hR'H
  rw [integral_physical_sq]
  refine le_of_eq_of_le (integral_congr_ae (ae_restrict_of_ae ?_))
    (cell_indicator_sq_le ((dyadicFiniteTree_mem_iff G J R' N).mp hR'J).1
      (eLpNorm_two_le_of_q (dyadicGridLength_pos G R'.1) hq (hfq R' hR'J hR'H')))
  filter_upwards [hF] with y hy
  rw [hy]

/-- The compression constant is monotone in the budget. -/
theorem compressionOneConst_le_of_budget {V : Type*} [Fintype V] (D' : ColumnTreeData V) {X : ℝ}
    (hX : D'.budget ≤ X) :
    compressionOneConst D' ≤
      (512 * ((1 : ℕ) + 1 : ℝ) ^ 512 * Real.log (2 * X)) ^ (512 * (1 + 1)) := by
  unfold compressionOneConst
  have h2 := D'.two_le_budget
  have hlog : Real.log (2 * D'.budget) ≤ Real.log (2 * X) :=
    Real.log_le_log (by linarith) (by linarith)
  have h0 : 0 ≤ Real.log (2 * D'.budget) := Real.log_nonneg (by linarith)
  gcongr

/-- Predictor packages persist under larger budgets and complexity exponents. -/
noncomputable def PredictorPackage.mono {κ : LocalKernelClass} {d e : ℕ}
    {A : QuadraticChartData d} {A' : QuadraticChartData e} {a i k b : Fin 4} {B D D' : ℝ}
    {c₁ c₁' : ℕ} (P : PredictorPackage κ A A' a i k b B D c₁) (hD : D ≤ D') (hc : c₁ ≤ c₁') :
    PredictorPackage κ A A' a i k b B D' c₁' where
  ι := P.ι
  L := P.L
  ψa := P.ψa
  ψb := P.ψb
  lam := P.lam
  coef := P.coef
  card_le := P.card_le.trans hD
  bdd := fun ℓ hℓ => by
    obtain ⟨h1, h2, h3, h4⟩ := P.bdd ℓ hℓ
    exact ⟨h1, h2, quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h3 hD) hc,
      quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h4 hD) hc⟩
  coef_le := fun r => (P.coef_le r).trans hD
  lam_le := fun ℓ r h => (P.lam_le ℓ r h).trans hD
  approx := P.approx

/-- A deep enough tree cell below `R` lies in the coarse tree rooted at `R`. -/
theorem mem_coarse_below {G : RealDyadicGrid} {J R I : ℤ × ℤ} {N K₀ : ℕ}
    (hR : R ∈ dyadicFiniteTree G J N)
    (hIR : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2) (hK : I.1 + K₀ ≤ J.1 + N) :
    K₀ ≤ dyadicRemainingDepth J N R ∧
      I ∈ dyadicFiniteTree G R (dyadicRemainingDepth J N R - K₀) := by
  have hend := dyadicRemainingDepth_endpoint G J N hR
  have hRI := dyadicGridCell_depth_le_of_subset G I R hIR
  have hK₀ : K₀ ≤ dyadicRemainingDepth J N R := by omega
  refine ⟨hK₀, (dyadicFiniteTree_mem_iff G R I _).mpr ⟨hIR, ?_⟩⟩
  have : ((dyadicRemainingDepth J N R - K₀ : ℕ) : ℤ) = dyadicRemainingDepth J N R - K₀ := by
    push_cast [hK₀]; ring
  omega

/-! ### The base data on a first-level root -/

/-- The explicit bound for the compression constant of an accurate-fit system with `n` labels
and private weights at least `ε`. -/
noncomputable def compBound (n : ℕ) (ε : ℝ) : ℝ :=
  (512 * ((1 : ℕ) + 1 : ℝ) ^ 512 * Real.log (2 * (2 + n + n * (Real.sqrt ε)⁻¹))) ^ (512 * (1 + 1))

/-- The replacement error of the base data (blueprint prop:base, lines 1626-1632). -/
noncomputable def baseErr (κ : LocalKernelClass) (cXi cXk : ℕ) (D Bp ε : ℝ) (K₀ Wa Wb : ℕ)
    (Cga Cgb : ℝ) : ℝ :=
  (cXi * cXk : ℝ) *
    ((2 * Real.exp (-Bp) * (2 * (compBound Wa ε + K₀) + 1) +
        D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)) *
        (2 * (1 + Cgb) + 4) +
      (2 * Real.exp (-Bp) * (2 * (compBound Wb ε + K₀) + 1) +
        D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4)) *
        (2 * (2 * (compBound Wa ε + K₀) + Cga) + 4))

theorem errExpr_mono {c Bp D ε K xa xb xa' xb' Cga Cgb dl : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hxa : 0 ≤ xa) (hxb : 0 ≤ xb) (ha : xa ≤ xa') (hb : xb ≤ xb') (hCga : 0 ≤ Cga)
    (hCgb : 0 ≤ Cgb) (hD : 0 ≤ D) (hdl : 0 ≤ dl) (hε : 0 ≤ ε) :
    c * ((2 * Real.exp (-Bp) * (2 * (xa + K) + 1) + D ^ 2 * (dl * ε * (1 + D) ^ 4)) *
        (2 * (1 + Cgb) + 4) +
      (2 * Real.exp (-Bp) * (2 * (xb + K) + 1) + D ^ 2 * (dl * ε * (1 + D) ^ 4)) *
        (2 * (2 * (xa + K) + Cga) + 4)) ≤
    c * ((2 * Real.exp (-Bp) * (2 * (xa' + K) + 1) + D ^ 2 * (dl * ε * (1 + D) ^ 4)) *
        (2 * (1 + Cgb) + 4) +
      (2 * Real.exp (-Bp) * (2 * (xb' + K) + 1) + D ^ 2 * (dl * ε * (1 + D) ^ 4)) *
        (2 * (2 * (xa' + K) + Cga) + 4)) := by
  have hE := (Real.exp_pos (-Bp)).le
  have h1 : 0 ≤ D ^ 2 * (dl * ε * (1 + D) ^ 4) :=
    mul_nonneg (sq_nonneg D) (mul_nonneg (mul_nonneg hdl hε) (pow_nonneg (by linarith) _))
  apply mul_le_mul_of_nonneg_left _ hc
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by linarith)
    gcongr
  · apply mul_le_mul _ _ (by linarith) (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hE)
      (by linarith)) h1)
    · gcongr
    · gcongr

/-- Blueprint prop:base on one first-level root `R`: with low lists below `R`, conjugate predictor
packages of lem:predictors (precision `B_p`, budget `D`), and tuple-specific accurate fits of
accuracies `k_a, k_b` (AccSetup.accurateFit) rooted at `R`, the cells `T_c` below `R` are covered
by active setups on roots of total length at most `8/3 |R|`, with the replacement error
`baseErr`, pair smallness, sizes, basic sides and the two-`U` term. -/
theorem baseFirstRoot (κ : LocalKernelClass) (c₀ : ℕ) (hc₀ : 1 ≤ c₀) :
    ∃ (c₁ C₁ c₂ Ca : ℕ), 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ ∀ q : ℝ, 2 < q → ∃ (Cqa : ℝ), 0 < Cqa ∧
    ∀ {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {H : ℝ} {R : ℤ × ℤ},
    R ∈ dyadicFiniteTree G J N → 1 ≤ H →
    ∀ {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
    ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ),
    (∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
    ∀ (f : Fin 4 → ℝ → ℂ), (∀ l, Measurable (f l)) →
    (∀ l, ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1) →
    ∀ (Xi Xk Xga Xgb : LowList G J N R c₀ H),
    (∃ (d : ℕ) (Φ : QuadraticChartData d), 1 ≤ d ∧ QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ) →
    ∀ (zga zgb : ℤ × ℤ → ℝ → ℂ) {Cga Cgb : ℝ}, 0 ≤ Cga → 0 ≤ Cgb →
    ((∀ I, Measurable (zga I) ∧ MemLp (zga I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f a) zga Cga ∧ HasDepthEnergy G J' (f a) zga 1) →
    ((∀ I, Measurable (zgb I) ∧ MemLp (zgb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f b) zgb Cgb ∧ HasDepthEnergy G J' (f b) zgb 1) →
    ∀ (K₀ : ℕ) (Tc : Finset (ℤ × ℤ)),
    (∀ I ∈ Tc, I ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 ∧ I.1 + K₀ ≤ J.1 + N ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zga I y = Xga.val I y) ∧
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y)) →
    (∀ I ∈ Tc, kernelHull G J N w I) → ∀ {Bd : ℝ},
    (∃ z₁ z₂, IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c₀ H w z₁ ∧
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c₀ H w z₂ ∧ ∀ I ∈ Tc, ∀ᵐ y ∂volume,
        y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y) →
    (∃ z₁ z₂, IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c₀ H w z₁ ∧
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c₀ H w z₂ ∧ ∀ I ∈ Tc, ∀ᵐ y ∂volume,
        y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y) →
    IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c₀ H w zga →
    IsBasicOn G R (dyadicRemainingDepth J N R) 1 Bd c₀ H w zgb →
    Bd ≤ 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ : ℕ) : ℝ) →
    (∀ I ∈ Tc, eLpNorm (Xi.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2) →
    (∀ I ∈ Tc, eLpNorm (Xk.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2) →
    (∀ I ∈ Tc, eLpNorm (Xga.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1) →
    (∀ I ∈ Tc, eLpNorm (Xgb.val I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1) →
    ∀ {η₀ : ℝ}, 0 ≤ η₀ →
    (∀ I ∈ Tc, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s'
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s)
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s') η₀) →
    ∀ (Bp ε : ℝ) (ka kb Ma Mb : ℕ), 1 ≤ Bp → 0 < ε → ε ≤ 1 → 1 ≤ ka → 1 ≤ kb →
    16 * fitBudget Cqa Ca ka ^ 2 < Ma → 16 * fitBudget Cqa Ca kb ^ 2 < Mb →
    let D := max H (Real.exp (C₁ * (1 + Bp + Real.log H) ^ C₁))
    let Wa := Fintype.card Xi.Λ * Fintype.card Xk.Λ * ⌊D⌋₊ + Ma
    let Wb := Fintype.card Xi.Λ * Fintype.card Xk.Λ * ⌊D⌋₊ + Mb
    let S₀ : ℝ := 1 + Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ
    let Sp : ℝ := Wa * Real.sqrt (2 ^ K₀ / ε) + 1
    ∃ (P : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (A : P → ActiveSetup κ (max (max c₁ c₀) c₂)),
      ∑ p : P, dyadicGridLength G (A p).R.1 ≤ 8 / 3 * dyadicGridLength G R.1 ∧
      (∀ I ∈ Tc, ∃ p : P, I ∈ (A p).cells) ∧
      (∀ p p' : P, ∀ I, I ∈ (A p).cells → I ∈ (A p').cells → p = p') ∧
      ∀ p : P, (A p).cells ⊆ Tc ∧
        (∀ I ∈ (A p).cells, ∀ J' ∈ Tc, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 →
          dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A p).cells) ∧
        (A p).G = G ∧ (A p).w = w ∧ (A p).a = a ∧ (A p).b = b ∧
        (A p).R ∈ dyadicFiniteTree G J N ∧
        dyadicGridCell G (A p).R.1 (A p).R.2 ⊆ dyadicGridCell G R.1 R.2 ∧
        (A p).H = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧
        (A p).Dc = Real.sqrt ε⁻¹ ∧ (A p).S = 2 ∧ (A p).η = 4 * η₀ ∧
        Fintype.card (A p).L = Fintype.card Xi.Λ + Fintype.card Xk.Λ +
          (Wa + Fintype.card Xga.Λ) + (Wb + Fintype.card Xgb.Λ) ∧
        ∑ I ∈ (A p).cells, dyadicGridLength G I.1 *
          ‖localProgressionForm (dyadicGridLength G I.1) (w I)
              (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I)) -
            (A p).Hf I ((A p).Y I)‖ ≤
          baseErr κ (Fintype.card Xi.Λ) (Fintype.card Xk.Λ) D Bp ε K₀ Wa Wb Cga Cgb *
            dyadicGridLength G (A p).R.1 ∧
        (∀ I ∈ (A p).cells, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
          (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A p).Y I s')
          (η₀ + (2 + 2 * S₀) * (Real.exp (-(ka : ℝ)) + Real.exp (-(kb : ℝ))) +
            (1 + Sp) * Real.exp (-(kb : ℝ)))) ∧
        (∀ I ∈ (A p).cells, ∀ l, (eLpNorm ((A p).Y I l) 2 ((A p).μ I)).toReal ≤ 2) ∧
        (∀ l, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 *
          (eLpNorm ((A p).U l I) 2 ((A p).μ I)).toReal ^ 2 ≤
            (K₀ : ℝ) ^ 2 * dyadicGridLength G (A p).R.1) ∧
        ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).z 3 I)‖ ≤
          η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G (A p).R.1) ∧
        (A p).HasColumnRep 1 ∧ (A p).SubRootProps η₀ ((K₀ : ℝ) ^ 2) := by
  obtain ⟨c₁, C₁, hc₁, hpkg⟩ := predictorPackage_nonempty c₀ hc₀ κ
  obtain ⟨c₂, Ca, hc₂, -, hacc⟩ := AccSetup.accurateFit κ
  refine ⟨c₁, C₁, c₂, Ca, hc₁, hc₂, fun q hq => ?_⟩
  obtain ⟨Cqa, hCqa, hacc'⟩ := hacc q hq
  refine ⟨Cqa, hCqa, ?_⟩
  intro G J N H R hR hH a i k b hai hak hab hik hib hkb w hw f hfm hfq Xi Xk Xga Xgb hdef₀ zga zgb
    Cga Cgb hCga hCgb hzga hzgb K₀ Tc hTc hTcH Bd hri hrk hrga hrgb hBd hLi hLk hLga hLgb η₀ hη₀
    hpairs
    Bp ε
    ka kb Ma Mb hBp hε0 hε1 hka1 hkb1 hMa hMb D Wa Wb S₀ Sp
  classical
  -- the empty case
  by_cases hTe : Tc = ∅
  · subst hTe
    refine ⟨∅, fun p => absurd p.2 (Finset.notMem_empty _), ?_, ?_, ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact mul_nonneg (by norm_num) (dyadicGridLength_pos G R.1).le
    · intro I hI; exact absurd hI (Finset.notMem_empty _)
    · intro p; exact absurd p.2 (Finset.notMem_empty _)
    · intro p; exact absurd p.2 (Finset.notMem_empty _)
  obtain ⟨I₀, hI₀⟩ := Finset.nonempty_iff_ne_empty.mpr hTe
  set N' := dyadicRemainingDepth J N R with hN'
  have hK₀ : K₀ ≤ N' := (mem_coarse_below hR (hTc I₀ hI₀).2.1 (hTc I₀ hI₀).2.2.1).1
  have hbelow : ∀ c, c ∈ dyadicFiniteTree G R N' ↔
      c ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G R.1 R.2 :=
    dyadicFiniteTree_below_iff G J N hR
  -- the low lists below `R`
  set! Xi' := Xi.reroot hR
  set! Xk' := Xk.reroot hR
  set! Xga' := Xga.reroot hR
  set! Xgb' := Xgb.reroot hR
  -- the predictor packages
  have hD : H ≤ D := le_max_left _ _
  have hD1 : 1 ≤ D := le_trans hH hD
  have hc₁' : c₁ ≤ max c₁ c₀ := le_max_left _ _
  have hD₀ : Real.exp (C₁ * (1 + Bp + Real.log H) ^ C₁) ≤ D := le_max_right _ _
  let pkga : ∀ (K K' : ℤ × ℤ) (li : Xi'.Λ) (lk : Xk'.Λ),
      PredictorPackage κ (Xi'.chart K li) (Xk'.chart K' lk) a i k b Bp D (max c₁ c₀) :=
    fun K K' li lk => (Classical.choice (hpkg H Bp (Xi'.chart K li) (Xk'.chart K' lk)
      (Xi'.one_le_dim K li) (Xk'.one_le_dim K' lk) (Xi'.complexity K li) (Xk'.complexity K' lk)
      (Xi'.bounded K li) (Xk'.bounded K' lk) hBp hai hak hab hik hib hkb)).mono hD₀ hc₁'
  let pkgb : ∀ (K K' : ℤ × ℤ) (li : Xi'.Λ) (lk : Xk'.Λ),
      PredictorPackage κ (Xi'.chart K li) (Xk'.chart K' lk) b i k a Bp D (max c₁ c₀) :=
    fun K K' li lk => (Classical.choice (hpkg H Bp (Xi'.chart K li) (Xk'.chart K' lk)
      (Xi'.one_le_dim K li) (Xk'.one_le_dim K' lk) (Xi'.complexity K li) (Xk'.complexity K' lk)
      (Xi'.bounded K li) (Xk'.bounded K' lk) hBp hib.symm hkb.symm hab.symm hik hai.symm
      hak.symm)).mono hD₀ hc₁'
  -- the accurate fits
  have hRH : kernelHull G J N w R := (hTcH I₀ hI₀).mono (hTc I₀ hI₀).2.1
  have hfn : ∀ l, ∀ c ∈ dyadicFiniteTree G R N', (c = R ∨ kernelHull G R N' w c) →
      eLpNorm (f l) 2
        (normalizedIntervalMeasure (dyadicGridLeft G c.1 c.2) (dyadicGridLength G c.1)) ≤ 1 :=
    fun l c hc hcH => eLpNorm_two_le_of_q (dyadicGridLength_pos G c.1) hq.le
      (hfq l c ((hbelow c).mp hc).1 (by
        rcases hcH with rfl | hcH
        · exact hRH
        · exact (kernelHull_below_iff hR ((hbelow c).mp hc).2).mp hcH))
  obtain ⟨hSa, hrootsA, hsegA⟩ := hacc' (predAccSetup κ Xi' Xk' a i k b Bp D pkga hε0 hε1 K₀ Ma
    (f a) w q ka c₂ (fitBudget Cqa Ca ka)) rfl rfl rfl hka1 (hfm a) (hfn a) hK₀ hw hMa
  obtain ⟨hSb, hrootsB, hsegB⟩ := hacc' (predAccSetup κ Xi' Xk' b i k a Bp D pkgb hε0 hε1 K₀ Mb
    (f b) w q kb c₂ (fitBudget Cqa Ca kb)) rfl rfl rfl hkb1 (hfm b) (hfn b) hK₀ hw hMb
  -- the active setups
  have hdef₀' : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ := by
    obtain ⟨d, Φ, -, h1, h2⟩ := hdef₀; exact ⟨d, Φ, h1, h2⟩
  have hcoarse : ∀ I ∈ Tc, I ∈ dyadicFiniteTree G R (N' - K₀) := fun I hI =>
    (mem_coarse_below hR (hTc I hI).2.1 (hTc I hI).2.2.1).2
  have hseg := baseSegments κ Xi' Xk' Bp D pkga pkgb hε0 hε1 hai hak hab hik hib hkb hD1 K₀ Ma Mb
    f w q ka kb c₂ (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb) hSa hSb hw Xga' Xgb' zga zgb hCga
    hCgb ⟨hzga.1, fun J' hJ' => hzga.2 J' ((hbelow J').mp hJ').1 ((hbelow J').mp hJ').2⟩
    ⟨hzgb.1, fun J' hJ' => hzgb.2 J' ((hbelow J').mp hJ').1 ((hbelow J').mp hJ').2⟩ Tc
    (fun I hI => ⟨hcoarse I hI, (hTc I hI).2.2.2.1, (hTc I hI).2.2.2.2⟩)
    (fun I hI => (kernelHull_below_iff hR (hTc I hI).2.1).mpr (hTcH I hI)) hq.le hfm
    (fun I hI l => hfq l I (hTc I hI).1 (hTcH I hI)) hLi hLk hLga hLgb hη₀ (Real.exp_pos _).le
    (Real.exp_pos _).le hpairs (fun I hI => (hsegA I (hcoarse I hI)).2.2)
    (fun I hI => (hsegB I (hcoarse I hI)).2.2) (c' := max (max c₁ c₀) c₂)
    (H' := max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)))
    (le_trans (le_max_right c₁ c₀) (le_max_left _ _)) (le_max_left _ _) (le_max_right _ _)
    (le_trans hD (le_max_left _ _)) (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))
    hdef₀' hri hrk hrga hrgb hBd (le_trans (le_max_right c₁ c₀) (le_max_left _ _))
    (le_trans hD (le_max_left _ _))
  dsimp only at hseg
  obtain ⟨P, A, hpack, hcover, hdisj, hA⟩ := hseg
  have hWa : Fintype.card (predAccSetup κ Xi' Xk' a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      (fitBudget Cqa Ca ka)).W = Wa := by
    change Fintype.card (Xi'.Λ × Xk'.Λ × Fin ⌊D⌋₊ ⊕ Fin Ma) = _
    rw [Fintype.card_eq_nat_card, Nat.card_sum, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Wa]
    rw [mul_assoc]
    rfl
  have hWb : Fintype.card (predAccSetup κ Xi' Xk' b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      (fitBudget Cqa Ca kb)).W = Wb := by
    change Fintype.card (Xi'.Λ × Xk'.Λ × Fin ⌊D⌋₊ ⊕ Fin Mb) = _
    rw [Fintype.card_eq_nat_card, Nat.card_sum, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Wb]
    rw [mul_assoc]
    rfl
  refine ⟨P, A, hpack, hcover, hdisj, fun p => ?_⟩
  obtain ⟨hcells, hclos, hG, hw', ha, hb, hRp, hH', hDc, hS, hη, hcard, hrep, hpair, hsize,
    hside, htwo, hcol, hsr⟩ := hA p
  refine ⟨hcells, hclos, hG, hw', ha, hb, ((hbelow _).mp hRp).1, ((hbelow _).mp hRp).2, hH',
    hDc, hS,
    hη, ?_, ?_, ?_, hsize, hside, htwo, hcol, hsr⟩
  · rw [hcard, hWa, hWb]; rfl
  · refine hrep.trans (mul_le_mul_of_nonneg_right ?_ (dyadicGridLength_pos G _).le)
    have hcomp : ∀ (V : Type) [Fintype V] (D' : ColumnTreeData V),
        0 ≤ compressionOneConst D' := by
      intro V _ D'
      unfold compressionOneConst
      exact pow_nonneg (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith only [D'.two_le_budget]))) _
    have hwA : ∀ v, ε ≤ (predAccSetup κ Xi' Xk' a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
        (fitBudget Cqa Ca ka)).wt v := by
      intro v; cases v with
      | inl v => exact le_rfl
      | inr m => exact hε1
    have hwB : ∀ v, ε ≤ (predAccSetup κ Xi' Xk' b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
        (fitBudget Cqa Ca kb)).wt v := by
      intro v; cases v with
      | inl v => exact le_rfl
      | inr m => exact hε1
    have hbA := ((predAccSetup κ Xi' Xk' a i k b Bp D pkga hε0 hε1 K₀ Ma (f a) w q ka c₂
      (fitBudget Cqa Ca ka)).system R).budget_le hε0 hwA
    have hbB := ((predAccSetup κ Xi' Xk' b i k a Bp D pkgb hε0 hε1 K₀ Mb (f b) w q kb c₂
      (fitBudget Cqa Ca kb)).system R).budget_le hε0 hwB
    rw [hWa] at hbA
    rw [hWb] at hbB
    have hca := compressionOneConst_le_of_budget (((predAccSetup κ Xi' Xk' a i k b Bp D pkga hε0
      hε1 K₀ Ma (f a) w q ka c₂ (fitBudget Cqa Ca ka)).system R).rooted R) hbA
    have hcb := compressionOneConst_le_of_budget (((predAccSetup κ Xi' Xk' b i k a Bp D pkgb hε0
      hε1 K₀ Mb (f b) w q kb c₂ (fitBudget Cqa Ca kb)).system R).rooted R) hbB
    have he2 : 0 ≤ (2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε :=
      add_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    exact errExpr_mono (by positivity) (Nat.cast_nonneg _) (hcomp _ _) (hcomp _ _) hca hcb hCga
      hCgb (by linarith only [hH, hD]) (delayConst_nonneg κ) he2
  · intro I hI s s' hss
    have := hpair I hI s s' hss
    rw [hWa] at this
    exact this

namespace LowList
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ c₀' : ℕ} {H H' : ℝ}

/-! ### Enlarging the complexity of low lists -/

/-- A low list of complexity `(c₀, H)` is one of complexity `(c₀', H')` for larger parameters. -/
noncomputable def mono (X : LowList G J N R c₀ H) (hc : c₀ ≤ c₀') (hH : H ≤ H') :
    LowList G J N R c₀' H' where
  Λ := X.Λ
  coef := X.coef
  coef_le := X.coef_le
  avail := X.avail
  coef_avail := X.coef_avail
  avail_mono := X.avail_mono
  birth := X.birth
  dim := X.dim
  chart := X.chart
  birth_spec := X.birth_spec
  avail_birth := X.avail_birth
  birth_canon' := X.birth_canon'
  one_le_dim := X.one_le_dim
  complexity := fun K l =>
    quadraticChartComplexity_order_mono (quadraticChartComplexity_mono (X.complexity K l) hH) hc
  bounded := X.bounded

theorem sub_card (X Y : LowList G J N R c₀ H) :
    Fintype.card (X.sub Y).Λ = Fintype.card X.Λ + Fintype.card Y.Λ := by
  change Fintype.card (X.Λ ⊕ Y.Λ) = _
  exact Fintype.card_sum

end LowList

/-- The cells of one generation have total length the root length. -/
theorem sum_dyadicGeneration_length (G : RealDyadicGrid) (J : ℤ × ℤ) (n : ℕ) :
    ∑ c ∈ dyadicGeneration G J n, dyadicGridLength G c.1 = dyadicGridLength G J.1 := by
  have h := measure_biUnion_finset (dyadicGeneration_pairwiseDisjoint G J n)
    (fun c _ => dyadicGridCell_measurable G c.1 c.2) (μ := volume)
  rw [dyadicGeneration_union, dyadicGridCell_volume] at h
  simp_rw [dyadicGridCell_volume] at h
  rw [← ENNReal.ofReal_sum_of_nonneg fun c _ => (dyadicGridLength_pos G c.1).le] at h
  exact ((ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun c _ =>
    (dyadicGridLength_pos G c.1).le) (dyadicGridLength_pos G J.1).le).mp h.symm)

/-- The cells of the last `K₀` levels of the tree have total length at most `K₀ |J|`. -/
theorem sum_bottom_length_le (G : RealDyadicGrid) (J : ℤ × ℤ) (N K₀ : ℕ) :
    ∑ I ∈ (dyadicFiniteTree G J N).filter (fun I => J.1 + N < I.1 + K₀),
      dyadicGridLength G I.1 ≤ K₀ * dyadicGridLength G J.1 := by
  classical
  set Q := (Finset.range (N + 1)).filter (fun n => N < n + K₀)
  have hsub : (dyadicFiniteTree G J N).filter (fun I => J.1 + N < I.1 + K₀) ⊆
      Q.biUnion (dyadicGeneration G J) := by
    intro I hI
    obtain ⟨hIT, hIb⟩ := Finset.mem_filter.mp hI
    obtain ⟨n, hn, hIn⟩ := Finset.mem_biUnion.mp hIT
    have hd := dyadicGeneration_depth G J n hIn
    refine Finset.mem_biUnion.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, by omega⟩, hIn⟩
  have hdisj : (Q : Set ℕ).PairwiseDisjoint (dyadicGeneration G J) := by
    intro n _ m _ hnm
    refine Finset.disjoint_left.mpr fun c hcn hcm => hnm ?_
    have := dyadicGeneration_depth G J n hcn
    have := dyadicGeneration_depth G J m hcm
    omega
  have hQ : (Q.card : ℝ) ≤ K₀ := by
    have : Q ⊆ Finset.Ico (N + 1 - K₀) (N + 1) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
      rw [Finset.mem_range] at hn1
      exact Finset.mem_Ico.mpr ⟨by omega, hn1⟩
    have h := Finset.card_le_card this
    rw [Nat.card_Ico] at h
    exact_mod_cast h.trans (by omega)
  calc ∑ I ∈ (dyadicFiniteTree G J N).filter (fun I => J.1 + N < I.1 + K₀),
        dyadicGridLength G I.1
      ≤ ∑ I ∈ Q.biUnion (dyadicGeneration G J), dyadicGridLength G I.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => (dyadicGridLength_pos G c.1).le
    _ = ∑ n ∈ Q, ∑ c ∈ dyadicGeneration G J n, dyadicGridLength G c.1 := Finset.sum_biUnion hdisj
    _ = Q.card * dyadicGridLength G J.1 := by
        simp only [sum_dyadicGeneration_length, Finset.sum_const, nsmul_eq_mul]
    _ ≤ K₀ * dyadicGridLength G J.1 :=
        mul_le_mul_of_nonneg_right hQ (dyadicGridLength_pos G J.1).le

theorem compBound_nonneg (n : ℕ) (ε : ℝ) : 0 ≤ compBound n ε := by
  unfold compBound
  have : (1 : ℝ) ≤ 2 * (2 + n + n * (Real.sqrt ε)⁻¹) := by
    have := Real.sqrt_nonneg ε
    have : (0 : ℝ) ≤ n * (Real.sqrt ε)⁻¹ := by positivity
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact pow_nonneg (mul_nonneg (by positivity) (Real.log_nonneg this)) _

theorem compBound_mono {n n' : ℕ} (h : n ≤ n') (ε : ℝ) : compBound n ε ≤ compBound n' ε := by
  unfold compBound
  have hs : (0 : ℝ) ≤ (Real.sqrt ε)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg ε)
  have hn : (n : ℝ) ≤ n' := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (1 : ℝ) ≤ 2 * (2 + n + n * (Real.sqrt ε)⁻¹) := by nlinarith only [hs]
  have hlog : Real.log (2 * (2 + n + n * (Real.sqrt ε)⁻¹)) ≤
      Real.log (2 * (2 + n' + n' * (Real.sqrt ε)⁻¹)) :=
    Real.log_le_log (by linarith) (by nlinarith only [hs, hn])
  have := Real.log_nonneg h1
  gcongr

theorem baseErr_mono (κ : LocalKernelClass) {ci ck ci' ck' : ℕ} {D Bp ε : ℝ} {K₀ Wa Wb Wa' Wb' : ℕ}
    {Cga Cgb Cga' Cgb' : ℝ} (hci : ci ≤ ci') (hck : ck ≤ ck') (hWa : Wa ≤ Wa') (hWb : Wb ≤ Wb')
    (hCga : 0 ≤ Cga) (hCgb : 0 ≤ Cgb) (hCga' : Cga ≤ Cga') (hCgb' : Cgb ≤ Cgb') (hD : 0 ≤ D) :
    baseErr κ ci ck D Bp ε K₀ Wa Wb Cga Cgb ≤ baseErr κ ci' ck' D Bp ε K₀ Wa' Wb' Cga' Cgb' := by
  unfold baseErr
  have hdl := delayConst_nonneg κ
  have he2 : 0 ≤ (2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε := by positivity
  have hT : 0 ≤ D ^ 2 * (delayConst κ * ((2 : ℝ)⁻¹ ^ K₀ + (1 + K₀) * Real.sqrt ε) * (1 + D) ^ 4) :=
    mul_nonneg (sq_nonneg D) (mul_nonneg (mul_nonneg hdl he2) (pow_nonneg (by linarith) _))
  have hcc : (ci * ck : ℝ) ≤ ci' * ck' := by
    have h1 : (ci : ℝ) ≤ ci' := by exact_mod_cast hci
    have h2 : (ck : ℝ) ≤ ck' := by exact_mod_cast hck
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact err_mono_real (by positivity) hcc (Real.exp_pos _).le hT (Nat.cast_nonneg _)
    (compBound_nonneg _ _) (compBound_nonneg _ _) (compBound_mono hWa ε) (compBound_mono hWb ε)
    hCga hCgb hCga' hCgb'

theorem baseErr_nonneg (κ : LocalKernelClass) (ci ck : ℕ) {D : ℝ} (Bp : ℝ) {ε : ℝ} (K₀ Wa Wb : ℕ)
    {Cga Cgb : ℝ} (hD : 0 ≤ D) (hCga : 0 ≤ Cga) (hCgb : 0 ≤ Cgb) :
    0 ≤ baseErr κ ci ck D Bp ε K₀ Wa Wb Cga Cgb := by
  have h := baseErr_mono κ (ci := 0) (ck := 0) (ci' := ci) (ck' := ck) (D := D) (Bp := Bp)
    (ε := ε) (K₀ := K₀) (Wa := Wa) (Wb := Wb) (Wa' := Wa) (Wb' := Wb) (Cga := Cga) (Cgb := Cgb)
    (Cga' := Cga) (Cgb' := Cgb) (Nat.zero_le _) (Nat.zero_le _) le_rfl le_rfl hCga hCgb le_rfl
    le_rfl hD
  refine le_trans (le_of_eq ?_) h
  unfold baseErr
  simp

namespace LowList
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {R : ℤ × ℤ} {c₀ : ℕ} {H : ℝ}

/-- The empty low list (no previous fit of a slot before its first update). -/
noncomputable def empty : LowList G J N R c₀ H where
  Λ := Empty
  coef := fun _ l => l.elim
  coef_le := fun _ l => l.elim
  avail := fun _ l => l.elim
  coef_avail := fun _ l => l.elim
  avail_mono := fun _ _ l => l.elim
  birth := fun _ l => l.elim
  dim := fun _ l => l.elim
  chart := fun _ l => l.elim
  birth_spec := fun _ l => l.elim
  avail_birth := fun _ l => l.elim
  birth_canon' := fun _ _ l => l.elim
  one_le_dim := fun _ l => l.elim
  complexity := fun _ l => l.elim
  bounded := fun _ l => l.elim

instance : IsEmpty (empty : LowList G J N R c₀ H).Λ := inferInstanceAs (IsEmpty Empty)

theorem empty_val (I : ℤ × ℤ) : (empty : LowList G J N R c₀ H).val I = 0 := by
  funext y; simp only [val, Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]

theorem empty_card : Fintype.card (empty : LowList G J N R c₀ H).Λ = 0 :=
  Fintype.card_eq_zero

end LowList

theorem ColumnDepthFamily.currentZ_measurable {V : Type*} [Fintype V] (Ψ : ColumnDepthFamily V)
    (Z : ColumnL2 V) (I : ℤ × ℤ) : Measurable (Ψ.currentZ Z I) := by
  classical
  unfold ColumnDepthFamily.currentZ
  split_ifs with h
  · have hm := (Lp.stronglyMeasurable (cellColumnProjection Ψ.D Ψ.A h Z)).measurable
    exact (EuclideanSpace.proj (𝕜 := ℂ) (none : Option V)).continuous.measurable.comp hm
  · exact measurable_const

theorem IsBasicOn.measurable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {CF Bd : ℝ} {c : ℕ}
    {Hc : ℝ} {w : ℤ × ℤ → ℝ × ℝ → ℂ} {z : ℤ × ℤ → ℝ → ℂ} (h : IsBasicOn G J N CF Bd c Hc w z)
    (I : ℤ × ℤ) : Measurable (z I) := by
  obtain ⟨V, _, Ψ, Z, -, -, -, -, -, hz⟩ := h
  rw [hz I]
  exact Ψ.currentZ_measurable Z I

/-! ### The bottom levels of the finite tree

Blueprint prop:base, eq:Y (lines 1600-1607) on the last `K₀` levels of a finite tree of depth `N`,
where the delayed projection `P^new_{e,s+K₀}` would act on cells below the tree. These cells are
grouped below fresh normalized segment roots `R` at most `K₀` levels above them, on which the new
high families are empty at depth `s` and complete (the identity) at depth `s + K₀` (recorded in
`automation/ErrorReport.md`). Then `Y_e = F_e - g_prev = X_e`, no replacement error arises, the
basic argument is `B_e = -g_prev` and the basic side is `U_e = F_e`, of energy at most `K₀ |R'|`
below every sub-root `R'`. -/

/-- The path column system without columns. -/
def emptyPathColumnSystem (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) :
    PathColumnSystem G J N Empty where
  avail := fun _ => ∅
  scalarAt := fun _ v => v.elim
  weight := fun v => v.elim
  weight_pos := fun v => v.elim
  weight_le := fun v => v.elim
  scalar_meas := fun _ v => v.elim
  scalar_bound := fun _ v => v.elim
  avail_mono := fun _ _ _ _ _ => Finset.Subset.refl _
  consistent := fun _ _ _ _ _ v => v.elim

theorem baseHighB_empty {G : RealDyadicGrid} {J : ℤ × ℤ} {N c₀ : ℕ} {H : ℝ}
    (X : LowList G J N J c₀ H) (Z : ColumnL2 Empty) (I : ℤ × ℤ) :
    baseHighB (emptyPathColumnSystem G J N) Z X.coef (fun I l => X.atom I l) I =
      fun y => -X.val I y := by
  funext y
  simp only [baseHighB, Finset.univ_eq_empty, Finset.sum_empty, zero_sub, LowList.val]

/-- The cells of a finite family below `R'` whose depths lie in `[R.1, R.1 + K₀)` with
`R' ⊆ R` have total length at most `K₀ |R'|`. -/
theorem sum_length_below_le {G : RealDyadicGrid} {R R' : ℤ × ℤ} {K₀ : ℕ}
    (hR' : dyadicGridCell G R'.1 R'.2 ⊆ dyadicGridCell G R.1 R.2) (S : Finset (ℤ × ℤ))
    (hS : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 ∧ I.1 < R.1 + K₀) :
    ∑ I ∈ S, dyadicGridLength G I.1 ≤ K₀ * dyadicGridLength G R'.1 := by
  classical
  have hRR' := dyadicGridCell_depth_le_of_subset G R' R hR'
  set N' : ℕ := (R.1 + K₀ - 1 - R'.1).toNat with hN'
  have hsub : S ⊆ (dyadicFiniteTree G R' N').filter (fun I => R'.1 + N' < I.1 + K₀) := by
    intro I hI
    obtain ⟨hIR', hId⟩ := hS I hI
    have hdI := dyadicGridCell_depth_le_of_subset G I R' hIR'
    refine Finset.mem_filter.mpr ⟨(dyadicFiniteTree_mem_iff G R' I N').mpr ⟨hIR', ?_⟩, ?_⟩
    · omega
    · omega
  calc ∑ I ∈ S, dyadicGridLength G I.1
      ≤ ∑ I ∈ (dyadicFiniteTree G R' N').filter (fun I => R'.1 + N' < I.1 + K₀),
          dyadicGridLength G I.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun I _ _ => (dyadicGridLength_pos G I.1).le
    _ ≤ K₀ * dyadicGridLength G R'.1 := sum_bottom_length_le G R' N' K₀



end TrilinearHT.Auto
end
