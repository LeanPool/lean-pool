/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec112cFiniteBaseDataAssembly.BaseRoot

/-!
# Trilinear Hilbert transform: baseBottom
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def BaseBottomHsubrootStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (c₀ : ℕ)
    (H : ℝ)
    (Xi : LowList G J N J c₀ H)
    (Xk : LowList G J N J c₀ H)
    (Xga : LowList G J N J c₀ H)
    (Xgb : LowList G J N J c₀ H)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (hai : a ≠ i)
    (hak : a ≠ k)
    (hab : a ≠ b)
    (hik : i ≠ k)
    (hib : i ≠ b)
    (hkb : k ≠ b)
    (K₀ : ℕ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (R : ℤ × ℤ)
    (T : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w I ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G R.1 R.2 ∧ I.1 < R.1 + (↑K₀ : ℤ))
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (c' : ℕ)
    (H' : ℝ)
    (ε : ℝ)
    (Bd : ℝ)
    (cB : ℕ)
    (HB : ℝ)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zga)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zgb)
    (_ : cB ≤ c')
    (_ : HB ≤ H')
    (_ : ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zga I y = Xga.val I y)
    (_ : ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y),
  let Pa : PathColumnSystem G J N Empty :=
    emptyPathColumnSystem G J N
  let Pb : PathColumnSystem G J N Empty :=
    emptyPathColumnSystem G J N
  ∀ (_ : Pb = emptyPathColumnSystem G J N),
  let Za : ↥(ColumnL2 Empty) :=
    (0 : ↥(ColumnL2 Empty))
  let Zb : ↥(ColumnL2 Empty) :=
    (0 : ↥(ColumnL2 Empty))
  ∀ (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N)
    (_ : ∀ I ∈ T, kernelHull G J N w I)
    (hsub : ∀ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2),
  let Ya : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then f a - Xga.val I else fun (y : ℝ) => -Xga.val I y
  let Yb : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then f b - Xgb.val I else fun (y : ℝ) => -Xgb.val I y
  ∀ (hYam : ∀ (I : ℤ × ℤ), Measurable (Ya I))
    (hYbm : ∀ (I : ℤ × ℤ), Measurable (Yb I))
    (hUa : ∀ (I : ℤ × ℤ), MemLp (Ya I - baseHighB Pa Za Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ)
      => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (hUb : ∀ (I : ℤ × ℤ), MemLp (Yb I - baseHighB Pb Zb Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ)
      => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (hUa' : ∀ (I : ℤ × ℤ), (eLpNorm (Ya I - baseHighB Pa Za Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (hUb' : ∀ (I : ℤ × ℤ), (eLpNorm (Yb I - baseHighB Pb Zb Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (hsmall : ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (Ya I)
      (Xi.val I) (Xk.val I) (Yb I))‖ ≤ (4 : ℝ) * η₀)
    (hdefc : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c' H' Φ ∧
      IsBoundedQuadraticChart Φ)
    (hlowc : ∀ (X : LowList G J N J c₀ H), PathCharts G T (fun (I : ℤ × ℤ) (l : X.Λ) => X.atom I
      l) (fun (I : ℤ × ℤ) (l : X.Λ) => X.coef I l ≠ (0 : ℂ)) c' H')
    (hPac' : PathCharts G T (fun (I : ℤ × ℤ) (v : Empty) => Pa.scalarAt I v) (fun (I : ℤ × ℤ) (v
      : Empty) => v ∈ Pa.avail I) c' H')
    (hPbc' : PathCharts G T (fun (I : ℤ × ℤ) (v : Empty) => Pb.scalarAt I v) (fun (I : ℤ × ℤ) (v
      : Empty) => v ∈ Pb.avail I) c' H')
    (hDc : (1 : ℝ) ≤ √ε⁻¹),
  let A : ActiveSetup κ c' :=
    baseActiveSetup κ Xi Xk Pa Pb Za Zb Xga.coef (fun I l => Xga.atom I l) Xgb.coef
        (fun I l => Xgb.atom I l) R T hsub w (fun I _ => hw I) hik hai.symm hib hak.symm hkb hab
        (fun I m => Xga.atom_measurable I m) (fun I m y => Xga.atom_bound I m y)
        (fun I m => Xgb.atom_measurable I m) (fun I m y => Xgb.atom_bound I m y) H'
        (hlowc Xi) (hlowc Xk) hPac' hPbc' (hlowc Xga) (hlowc Xgb) hdefc (Real.sqrt ε⁻¹) hDc
        (fun _ _ v => v.elim) (fun _ _ v => v.elim)
        Xga.coef_le Xgb.coef_le Ya Yb hYam hYbm 2 (by norm_num) hUa hUb hUa' hUb'
        (4 * η₀) hsmall
  ∀ (_ : dyadicGridCell G R.1 R.2 ⊆ dyadicGridCell G J.1 J.2)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ T, (eLpNorm (A.U l I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ) ≤ (1 : ℝ))
    (_ : ∀ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ / (2 : ℝ)
      * (dyadicGridLength G I.1 * (eLpNorm (A.U a I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ) + dyadicGridLength G I.1 * (eLpNorm (A.U b I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 :
      ℕ)))
    (_ : ∀ (R' : ℤ × ℤ), dyadicGridCell G R'.1 R'.2 ⊆ dyadicGridCell G R.1 R.2 → ∑ I ∈ T with
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2, dyadicGridLength G I.1 ≤
      (↑K₀ : ℝ) * dyadicGridLength G R'.1),
  let XB : ℝ :=
    (2 : ℝ) + (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Empty +
      Fintype.card Xga.Λ) + (Fintype.card Empty + Fintype.card Xgb.Λ)) : ℝ) * ((1 : ℝ) +
      √ε⁻¹)
  ∀ (_ : Bd ≤ XB),
  A.SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))


open scoped Classical in
private def BaseBottomStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (c₀ : ℕ)
    (H : ℝ)
    (Xi : LowList G J N J c₀ H)
    (Xk : LowList G J N J c₀ H)
    (Xga : LowList G J N J c₀ H)
    (Xgb : LowList G J N J c₀ H)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ i)
    (_ : a ≠ k)
    (_ : a ≠ b)
    (_ : i ≠ k)
    (_ : i ≠ b)
    (_ : k ≠ b)
    (K₀ : ℕ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (R : ℤ × ℤ)
    (_ : R ∈ dyadicFiniteTree G J N)
    (T : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w I ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G R.1 R.2 ∧ I.1 < R.1 + (↑K₀ : ℤ))
    (_ : ∀ I ∈ T, ∀ (l : Fin (4 : ℕ)), eLpNorm (slots4 a i k (f a - Xga.val I) (Xi.val I)
      (Xk.val I) (f b - Xgb.val I) l) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : ∀ I ∈ T, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s' (slots4 a i k (f a - Xga.val I) (Xi.val I)
      (Xk.val I) (f b - Xgb.val I) s) (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val
      I) (f b - Xgb.val I) s') η₀)
    (c' : ℕ)
    (H' : ℝ)
    (_ : c₀ ≤ c')
    (_ : H ≤ H')
    (_ : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ)
    (ε : ℝ)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ (1 : ℝ))
    (Bd : ℝ)
    (cB : ℕ)
    (HB : ℝ)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (_ : ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G J N (1 : ℝ) Bd cB HB w z₁ ∧
      IsBasicOn G J N (1 : ℝ) Bd cB HB w z₂ ∧ ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G
      I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (zga : ℤ × ℤ → ℝ → ℂ)
    (zgb : ℤ × ℤ → ℝ → ℂ)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zga)
    (_ : IsBasicOn G J N (1 : ℝ) Bd cB HB w zgb)
    (_ : Bd ≤ (2 : ℝ) + (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ) : ℝ))
    (_ : cB ≤ c')
    (_ : HB ≤ H')
    (_ : ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zga I y = Xga.val I y)
    (_ : ∀ I ∈ T, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y),
  let Pa : PathColumnSystem G J N Empty :=
    emptyPathColumnSystem G J N
  let Pb : PathColumnSystem G J N Empty :=
    emptyPathColumnSystem G J N
  ∀ (_ : Pb = emptyPathColumnSystem G J N),
  let Za : ↥(ColumnL2 Empty) :=
    (0 : ↥(ColumnL2 Empty))
  let Zb : ↥(ColumnL2 Empty) :=
    (0 : ↥(ColumnL2 Empty))
  ∀ (_ : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N)
    (_ : ∀ I ∈ T, kernelHull G J N w I)
    (_ : ∀ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2),
  let Ya : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then f a - Xga.val I else fun (y : ℝ) => -Xga.val I y
  let Yb : ℤ × ℤ → ℝ → ℂ :=
    fun (I : ℤ × ℤ) => if I ∈ T then f b - Xgb.val I else fun (y : ℝ) => -Xgb.val I y
  ∀ (_ : ∀ (I : ℤ × ℤ), Ya I - baseHighB Pa Za Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ) =>
      Xga.atom I l) I = if I ∈ T then f a else (0 : ℝ → ℂ))
    (_ : ∀ (I : ℤ × ℤ), Yb I - baseHighB Pb Zb Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ) =>
      Xgb.atom I l) I = if I ∈ T then f b else (0 : ℝ → ℂ))
    (_ : ∀ (I : ℤ × ℤ), Measurable (Ya I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (Yb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (Ya I - baseHighB Pa Za Xga.coef (fun (I : ℤ × ℤ) (l : Xga.Λ)
      => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (Yb I - baseHighB Pb Zb Xgb.coef (fun (I : ℤ × ℤ) (l : Xgb.Λ)
      => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ T, (eLpNorm (f l) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (1 : ℝ))
    (_ : ∀ (I : ℤ × ℤ), (eLpNorm (Ya I - baseHighB Pa Za Xga.coef (fun (I : ℤ × ℤ) (l :
      Xga.Λ) => Xga.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (_ : ∀ (I : ℤ × ℤ), (eLpNorm (Yb I - baseHighB Pb Zb Xgb.coef (fun (I : ℤ × ℤ) (l :
      Xgb.Λ) => Xgb.atom I l) I) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ (2 : ℝ))
    (_ : ∀ I ∈ T, slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I) = slots4 a i k (f a -
      Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I))
    (_ : ∀ I ∈ T, ∀ (Fa Fb : ℝ → ℂ), Measurable Fa → Measurable Fb → eLpNorm Fa (2 : ℝ≥0∞)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≠
      ∞ → eLpNorm Fb (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1)) ≠ ∞ → ‖localProgressionForm (dyadicGridLength G I.1) (w
      I) (slots4 a i k Fa (Xi.val I) (Xk.val I) Fb)‖ ≤ (eLpNorm Fa (2 : ℝ≥0∞)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1))).toReal * (eLpNorm Fb (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft
      G I.1 I.2) (dyadicGridLength G I.1))).toReal * η₀)
    (_ : ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 a i k (Ya I)
      (Xi.val I) (Xk.val I) (Yb I))‖ ≤ (4 : ℝ) * η₀),
  ∃ (A : ActiveSetup κ c'), A.G = G ∧ A.R = R ∧ A.cells = T ∧ A.w = w ∧ A.a = a ∧ A.b
    = b ∧ A.H = H' ∧ A.Dc = √ε⁻¹ ∧ A.S = (2 : ℝ) ∧ A.η = (4 : ℝ) * η₀ ∧ Fintype.card
    A.L = Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ + Fintype.card
    Xgb.Λ ∧ (∀ I ∈ T, A.Y I = slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f
    b - Xgb.val I)) ∧ (∀ I ∈ T, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
    (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' (A.Y I s) (A.Y I
    s') η₀) ∧ (∀ I ∈ T, ∀ (l : Fin (4 : ℕ)), (eLpNorm (A.Y I l) (2 : ℝ≥0∞) (A.μ
    I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ T, dyadicGridLength G I.1 *
    (eLpNorm (A.U l I) (2 : ℝ≥0∞) (A.μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G R.1) ∧ ∑ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z (3 : Fin
    (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G R.1) ∧
    A.HasColumnRep (1 : ℝ) ∧ A.SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))




private theorem baseBottom_hsubroot : BaseBottomHsubrootStatement := by
  classical
  intro κ G J N c₀ H Xi Xk Xga Xgb a i k b hai hak hab hik hib hkb K₀ f w hw R T hT η₀ hη₀ c' H' ε
    Bd cB HB hri hrk zga zgb hrga hrgb hcB hHB hzga hzgb Pa Pb hPb Za Zb hTtree hTH hsub Ya Yb
    hYam hYbm hUa hUb hUa' hUb' hsmall hdefc hlowc hPac' hPbc' hDc A hRJ hUsq hcell hK XB hBdX R'
    hR'
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
  · simp only [not_exists, not_and] at hne
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
  have hK1 : (1 : ℝ) ≤ K₀ := by
    have h1 := (hT I₀ hI₀).2.2.2
    have h2 := dyadicGridCell_depth_le_of_subset G I₀ R (hsub I₀ hI₀)
    exact_mod_cast (show 1 ≤ K₀ by omega)
  have hKK : (K₀ : ℝ) ≤ (K₀ : ℝ) ^ 2 := by nlinarith only [hK1]
  have hmem : ∀ I ∈ T.filter (fun I => dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2),
      I ∈ T ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 := fun I hI =>
    Finset.mem_filter.mp hI
  have hside : ∀ l, ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
      dyadicGridLength G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1 := by
    intro l
    calc ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
          dyadicGridLength G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2
        ≤ ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
          dyadicGridLength G I.1 := Finset.sum_le_sum fun I hI => by
            have := hUsq l I (hmem I hI).1
            have hr := dyadicGridLength_pos G I.1
            nlinarith only [this, hr]
      _ ≤ K₀ * dyadicGridLength G R'.1 := hK R' hR'
      _ ≤ (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1 :=
          mul_le_mul_of_nonneg_right hKK hR'pos.le
  have hR'tree : R' ∈ dyadicFiniteTree G J N := (dyadicFiniteTree_mem_iff G J R' N).mpr
    ⟨hR'.trans hRJ, (dyadicGridCell_depth_le_of_subset G I₀ R' hI₀R').trans
      ((dyadicFiniteTree_mem_iff G J I₀ N).mp (hTtree I₀ hI₀)).2⟩
  have hR'H : kernelHull G J N w R' := (hTH I₀ hI₀).mono hI₀R'
  refine ⟨hside, ?_, ?_⟩
  · calc ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
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
          (K₀ : ℝ) ^ 2 * dyadicGridLength G R'.1) := by gcongr <;> exact hside _
      _ = _ := by ring
  · obtain ⟨Pga, hPgab, hPgac, hPgae, hPga⟩ := hrga.basicProjection hR'tree hR'H
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
    apply baseActiveSetup_columnRepBelow (hX := le_rfl) (hri := hpair hri) (hrk := hpair hrk)
      (hra := ⟨Pga.zero zero_le_one, Pga, hPgab.trans hBdX, hPgab.trans hBdX,
        hPgac.mono hTs hcB hHB, hPgac.mono hTs hcB hHB, Pga.zero_cellEnergyOn zero_le_one _,
        hPgae.mono hTH', fun I hI hIR => ?_⟩)
      (hrb := ⟨Pgb.zero zero_le_one, Pgb, hPgbb.trans hBdX, hPgbb.trans hBdX,
        hPgbc.mono hTs hcB hHB, hPgbc.mono hTs hcB hHB, Pgb.zero_cellEnergyOn zero_le_one _,
        hPgbe.mono hTH', fun I hI hIR => ?_⟩)
    · filter_upwards [Pga.zero_val zero_le_one I, hzga I hI] with y h1 h2 hyI
      rw [← hPga I, h2 hyI, h1]
      simp [Pa, emptyPathColumnSystem, LowList.val]
    · filter_upwards [Pgb.zero_val zero_le_one I, hzgb I hI] with y h1 h2 hyI
      rw [← hPgb I, h2 hyI, h1]
      simp [Pb, emptyPathColumnSystem, LowList.val]



private theorem baseBottom_stage_1 : BaseBottomStage1Statement := by
  classical
  intro κ G J N c₀ H Xi Xk Xga Xgb a i k b hai hak hab hik hib hkb K₀ f w hw R hR T hT hsz η₀ hη₀
    hpairs c' H' hc₀ hHH hdef₀ ε hε0 hε1 Bd cB HB hri hrk zga zgb hrga hrgb hBd hcB hHB hzga hzgb
    Pa Pb hPb Za Zb hTtree hTH hsub Ya Yb hUaT hUbT hYam hYbm hUa hUb hfle hUa' hUb' hYT hlowpair
    hsmall
  have hdefc : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c' H' Φ ∧
      IsBoundedQuadraticChart Φ := by
    obtain ⟨d, Φ, h1, h2⟩ := hdef₀
    exact ⟨d, Φ, quadraticChartComplexity_order_mono (quadraticChartComplexity_mono h1 hHH) hc₀, h2⟩
  have hlowc : ∀ X : LowList G J N J c₀ H, PathCharts G T (fun I l => X.atom I l)
      (fun I l => X.coef I l ≠ 0) c' H' := fun X =>
    PathCharts.mono_c (((X.pathCharts T).mono (fun _ _ h => h) hHH)) hc₀
  have hPac' : PathCharts G T (fun I v => Pa.scalarAt I v) (fun I v => v ∈ Pa.avail I) c' H' :=
    ⟨fun _ _ v => v.elim, fun _ _ _ _ _ v => v.elim⟩
  have hPbc' : PathCharts G T (fun I v => Pb.scalarAt I v) (fun I v => v ∈ Pb.avail I) c' H' :=
    ⟨fun _ _ v => v.elim, fun _ _ _ _ _ v => v.elim⟩
  have hDc : 1 ≤ Real.sqrt ε⁻¹ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ((one_le_inv₀ hε0).mpr hε1)
  set! A := baseActiveSetup κ Xi Xk Pa Pb Za Zb Xga.coef (fun I l => Xga.atom I l) Xgb.coef
    (fun I l => Xgb.atom I l) R T hsub w (fun I _ => hw I) hik hai.symm hib hak.symm hkb hab
    (fun I m => Xga.atom_measurable I m) (fun I m y => Xga.atom_bound I m y)
    (fun I m => Xgb.atom_measurable I m) (fun I m y => Xgb.atom_bound I m y) H'
    (hlowc Xi) (hlowc Xk) hPac' hPbc' (hlowc Xga) (hlowc Xgb) hdefc (Real.sqrt ε⁻¹) hDc
    (fun _ _ v => v.elim) (fun _ _ v => v.elim)
    Xga.coef_le Xgb.coef_le Ya Yb hYam hYbm 2 (by norm_num) hUa hUb hUa' hUb'
    (4 * η₀) hsmall with hA
  have hY : ∀ I ∈ T, A.Y I = slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I) := fun I hI =>
    baseActiveSetup_Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ hI
  have hUa_eq : ∀ I, A.U a I = Ya I - baseHighB Pa Za Xga.coef (fun I l => Xga.atom I l) I :=
    fun I => baseActiveSetup_U_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I
  have hUb_eq : ∀ I, A.U b I = Yb I - baseHighB Pb Zb Xgb.coef (fun I l => Xgb.atom I l) I :=
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
  -- the basic sides are the inputs
  have hUsq : ∀ l, ∀ I ∈ T, (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤ 1 := by
    intro l I hI
    by_cases hla : l = a
    · rw [hla, hUa_eq, hUaT, ite_eq_left_of_eq_true _ _ (eq_true hI)]
      have h1 := hfle a I hI
      have h0 : (0 : ℝ) ≤ (eLpNorm (f a) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal := ENNReal.toReal_nonneg
      change (eLpNorm (f a) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal ^ 2 ≤ 1
      nlinarith only [h1, h0]
    by_cases hlb : l = b
    · rw [hlb, hUb_eq, hUbT, ite_eq_left_of_eq_true _ _ (eq_true hI)]
      have h1 := hfle b I hI
      have h0 : (0 : ℝ) ≤ (eLpNorm (f b) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal := ENNReal.toReal_nonneg
      change (eLpNorm (f b) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal ^ 2 ≤ 1
      nlinarith only [h1, h0]
    rw [hU0 l I hla hlb]
    simp
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
  have hK : ∀ R' : ℤ × ℤ, dyadicGridCell G R'.1 R'.2 ⊆ dyadicGridCell G R.1 R.2 →
      ∑ I ∈ T with dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2,
        dyadicGridLength G I.1 ≤ K₀ * dyadicGridLength G R'.1 := fun R' hR' =>
    sum_length_below_le hR' _ fun I hI =>
      ⟨(Finset.mem_filter.mp hI).2, (hT I (Finset.mem_filter.mp hI).1).2.2.2⟩
  -- the column budgets of the basic projections
  set! XB : ℝ := 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Empty +
    Fintype.card Xga.Λ) + (Fintype.card Empty + Fintype.card Xgb.Λ) : ℕ) : ℝ) *
      (1 + Real.sqrt ε⁻¹) with hXB
  have hBdX : Bd ≤ XB := by
    refine hBd.trans ?_
    have hsq0 : 0 ≤ Real.sqrt ε⁻¹ := Real.sqrt_nonneg _
    have hs : ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
        Fintype.card Xgb.Λ : ℕ) : ℝ) ≤ ((Fintype.card Xi.Λ + Fintype.card Xk.Λ +
          (Fintype.card Empty + Fintype.card Xga.Λ) + (Fintype.card Empty + Fintype.card Xgb.Λ) :
            ℕ) : ℝ) := by exact_mod_cast (by omega)
    have h0 : (0 : ℝ) ≤ ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + (Fintype.card Empty +
        Fintype.card Xga.Λ) + (Fintype.card Empty + Fintype.card Xgb.Λ) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [hXB]
    nlinarith only [mul_nonneg h0 hsq0, hs]
  have hsubroot : A.SubRootProps η₀ ((K₀ : ℝ) ^ 2) := by
    expose_names
    exact @baseBottom_hsubroot κ G J N c₀ H Xi Xk Xga Xgb a i k b hai hak hab hik hib hkb K₀ f w
      hw R T hT η₀ hη₀ c' H' ε Bd cB HB hri hrk zga zgb hrga hrgb hcB hHB hzga hzgb hPb hTtree hTH
      hsub hYam hYbm hUa hUb hUa' hUb' hsmall hdefc hlowc hPac' hPbc' hDc hRJ hUsq hcell hK hBdX
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
  have hYeq : ∀ I ∈ T, A.Y I =
      slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) := fun I hI => by
    rw [hY I hI, hYT I hI]
  refine ⟨A, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hYeq, ?_, ?_, hsideR, htwoR,
    A.hasColumnRep_of_below hcolR, hsubroot⟩
  · change Fintype.card (Xi.Λ ⊕ Xk.Λ ⊕ (Empty ⊕ Xga.Λ) ⊕ (Empty ⊕ Xgb.Λ)) = _
    simp only [Fintype.card_sum, Fintype.card_empty]
    ring
  · intro I hI s s' hss
    rw [hYeq I hI]
    exact hpairs I hI s s' hss
  · intro I hI l
    rw [hYeq I hI]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (hsz I hI l)


/-- Blueprint prop:base at the bottom levels of a finite tree (lines 1600-1616, with the new
families empty at depth `s` and complete at depth `s + K₀`): on cells `T` below `R` within `K₀`
levels of `R`, the tuple `X` itself is an active setup: `Y = X` (no replacement
error), every pair of `Y` is `η₀`-small, the normalized sizes are at most two, the basic sides
`U_e = F_e` satisfy `eq:basic-side` with constant `K₀²`, the two-`U` term is at most
`η₀ K₀² |R|`, and the basic arguments `X_i, X_k, -g_prev` are differences of two current basic
projections, also below every sub-root. -/
theorem baseBottom (κ : LocalKernelClass) {G : RealDyadicGrid} {J : ℤ × ℤ} {N c₀ : ℕ} {H : ℝ}
    (Xi Xk Xga Xgb : LowList G J N J c₀ H) {a i k b : Fin 4}
    (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b) (hkb : k ≠ b)
    (K₀ : ℕ) (f : Fin 4 → ℝ → ℂ) (hfm : ∀ l, Measurable (f l)) (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
      (w I))
    {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (T : Finset (ℤ × ℤ))
    (hT : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N ∧ kernelHull G J N w I ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 ∧ I.1 < R.1 + K₀)
    (hfn : ∀ l, ∀ I ∈ T, eLpNorm (f l) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1)
    (hsz : ∀ I ∈ T, ∀ l, eLpNorm (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I)
      (f b - Xgb.val I) l) 2 (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1)) ≤ ENNReal.ofReal 2)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hpairs : ∀ I ∈ T, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s'
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s)
      (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s') η₀)
    {c' : ℕ} {H' : ℝ} (hc₀ : c₀ ≤ c') (hHH : H ≤ H')
    (hdef₀ : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity c₀ H Φ ∧
      IsBoundedQuadraticChart Φ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {Bd : ℝ} {cB : ℕ} {HB : ℝ}
    (hri : ∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧ IsBasicOn G J N 1 Bd cB HB w z₂ ∧
      ∀ I ∈ T, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = z₁ I y - z₂ I y)
    (hrk : ∃ z₁ z₂, IsBasicOn G J N 1 Bd cB HB w z₁ ∧ IsBasicOn G J N 1 Bd cB HB w z₂ ∧
      ∀ I ∈ T, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y)
    (zga zgb : ℤ × ℤ → ℝ → ℂ) (hrga : IsBasicOn G J N 1 Bd cB HB w zga)
    (hrgb : IsBasicOn G J N 1 Bd cB HB w zgb)
    (hBd : Bd ≤ 2 + ((Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
      Fintype.card Xgb.Λ : ℕ) : ℝ)) (hcB : cB ≤ c') (hHB : HB ≤ H')
    (hzga : ∀ I ∈ T, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zga I y = Xga.val I y)
    (hzgb : ∀ I ∈ T, ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zgb I y = Xgb.val I y) :
    ∃ A : ActiveSetup κ c', A.G = G ∧ A.R = R ∧ A.cells = T ∧ A.w = w ∧ A.a = a ∧ A.b = b ∧
      A.H = H' ∧ A.Dc = Real.sqrt ε⁻¹ ∧ A.S = 2 ∧ A.η = 4 * η₀ ∧
      Fintype.card A.L = Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ +
        Fintype.card Xgb.Λ ∧
      (∀ I ∈ T, A.Y I = slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I)) ∧
      (∀ I ∈ T, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)
        (w I) s s' (A.Y I s) (A.Y I s') η₀) ∧
      (∀ I ∈ T, ∀ l, (eLpNorm (A.Y I l) 2 (A.μ I)).toReal ≤ 2) ∧
      (∀ l, ∑ I ∈ T, dyadicGridLength G I.1 * (eLpNorm (A.U l I) 2 (A.μ I)).toReal ^ 2 ≤
        (K₀ : ℝ) ^ 2 * dyadicGridLength G R.1) ∧
      ∑ I ∈ T, dyadicGridLength G I.1 * ‖A.Hf I (A.z 3 I)‖ ≤
        η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G R.1) ∧
      A.HasColumnRep 1 ∧ A.SubRootProps η₀ ((K₀ : ℝ) ^ 2) := by
  classical
  set! Pa := emptyPathColumnSystem G J N with hPa
  set Pb := emptyPathColumnSystem G J N with hPb
  set! Za : ColumnL2 Empty := 0
  set! Zb : ColumnL2 Empty := 0
  have hTtree : ∀ I ∈ T, I ∈ dyadicFiniteTree G J N := fun I hI => (hT I hI).1
  have hTH : ∀ I ∈ T, kernelHull G J N w I := fun I hI => (hT I hI).2.1
  have hsub : ∀ I ∈ T, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 := fun I hI =>
    (hT I hI).2.2.1
  have hBa : ∀ I, baseHighB Pa Za Xga.coef (fun I l => Xga.atom I l) I = fun y => -Xga.val I y :=
    fun I => baseHighB_empty Xga Za I
  have hBb : ∀ I, baseHighB Pb Zb Xgb.coef (fun I l => Xgb.atom I l) I = fun y => -Xgb.val I y :=
    fun I => baseHighB_empty Xgb Zb I
  -- the inputs: unreplaced on the cells, without side elsewhere
  set! Ya : ℤ × ℤ → ℝ → ℂ := fun I => if I ∈ T then f a - Xga.val I else fun y => -Xga.val I y
    with hYa_def
  set! Yb : ℤ × ℤ → ℝ → ℂ := fun I => if I ∈ T then f b - Xgb.val I else fun y => -Xgb.val I y
    with hYb_def
  have hUaT : ∀ I, Ya I - baseHighB Pa Za Xga.coef (fun I l => Xga.atom I l) I =
      if I ∈ T then f a else 0 := by
    intro I
    rw [hBa]
    funext y
    by_cases hI : I ∈ T <;> simp [hYa_def, hI]
  have hUbT : ∀ I, Yb I - baseHighB Pb Zb Xgb.coef (fun I l => Xgb.atom I l) I =
      if I ∈ T then f b else 0 := by
    intro I
    rw [hBb]
    funext y
    by_cases hI : I ∈ T <;> simp [hYb_def, hI]
  have hYam : ∀ I, Measurable (Ya I) := fun I => by
    simp only [hYa_def]; split_ifs
    · exact (hfm a).sub (Xga.val_measurable I)
    · exact (Xga.val_measurable I).neg
  have hYbm : ∀ I, Measurable (Yb I) := fun I => by
    simp only [hYb_def]; split_ifs
    · exact (hfm b).sub (Xgb.val_measurable I)
    · exact (Xgb.val_measurable I).neg
  have hfL : ∀ l, ∀ I ∈ T, MemLp (f l) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) :=
    fun l I hI => lt_of_le_of_lt (hfn l I hI) ENNReal.one_lt_top
  have hUa : ∀ I, MemLp (Ya I - baseHighB Pa Za Xga.coef (fun I l => Xga.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) := by
    intro I; rw [hUaT]; split_ifs with hI
    · exact hfL a I hI
    · exact MemLp.zero
  have hUb : ∀ I, MemLp (Yb I - baseHighB Pb Zb Xgb.coef (fun I l => Xgb.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) := by
    intro I; rw [hUbT]; split_ifs with hI
    · exact hfL b I hI
    · exact MemLp.zero
  have hfle : ∀ l, ∀ I ∈ T, (eLpNorm (f l) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1))).toReal ≤ 1 :=
    fun l I hI => by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (hfn l I hI)
      simpa using this
  have hUa' : ∀ I, (eLpNorm (Ya I - baseHighB Pa Za Xga.coef (fun I l => Xga.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal ≤ 2 := by
    intro I; rw [hUaT]; split_ifs with hI
    · linarith [hfle a I hI]
    · simp
  have hUb' : ∀ I, (eLpNorm (Yb I - baseHighB Pb Zb Xgb.coef (fun I l => Xgb.atom I l) I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2)
        (dyadicGridLength G I.1))).toReal ≤ 2 := by
    intro I; rw [hUbT]; split_ifs with hI
    · linarith [hfle b I hI]
    · simp
  have hYT : ∀ I ∈ T, slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I) =
      slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) := fun I hI => by
    simp only [hYa_def, hYb_def, hI, ↓reduceIte]
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
  have hsmall : ∀ I ∈ T, ‖localProgressionForm (dyadicGridLength G I.1) (w I)
      (slots4 a i k (Ya I) (Xi.val I) (Xk.val I) (Yb I))‖ ≤ 4 * η₀ := by
    intro I hI
    have ha := hsz I hI a
    have hb := hsz I hI b
    rw [slots4_a] at ha
    rw [slots4_b hab hib hkb] at hb
    rw [hYT I hI]
    refine (hlowpair I hI _ _ ((hfm a).sub (Xga.val_measurable I))
      ((hfm b).sub (Xgb.val_measurable I))
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)).trans ?_
    have ha' := ENNReal.toReal_le_of_le_ofReal (by norm_num) ha
    have hb' := ENNReal.toReal_le_of_le_ofReal (by norm_num) hb
    have := mul_le_mul ha' hb' ENNReal.toReal_nonneg (by norm_num)
    calc _ ≤ 2 * 2 * η₀ := mul_le_mul_of_nonneg_right this hη₀
      _ = _ := by ring
  -- path charts
  expose_names
  exact @baseBottom_stage_1 κ G J N c₀ H Xi Xk Xga Xgb a i k b hai hak hab hik hib hkb K₀ f w hw R
    hR T hT hsz η₀ hη₀ hpairs c' H' hc₀ hHH hdef₀ ε hε0 hε1 Bd cB HB hri hrk zga zgb hrga hrgb hBd
    hcB hHB hzga hzgb hPb hTtree hTH hsub hUaT hUbT hYam hYbm hUa hUb hfle hUa' hUb' hYT hlowpair
    hsmall

/-- The cells of one depth of a finite tree have total length at most the root length. -/
theorem sum_tree_depth_le (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (d : ℤ) :
    ∑ c ∈ (dyadicFiniteTree G J N).filter (fun c => c.1 = d), dyadicGridLength G c.1 ≤
      dyadicGridLength G J.1 := by
  classical
  by_cases hd : J.1 ≤ d
  · have hsub : (dyadicFiniteTree G J N).filter (fun c => c.1 = d) ⊆
        dyadicGeneration G J (d - J.1).toNat := by
      intro c hc
      obtain ⟨hcT, hcd⟩ := Finset.mem_filter.mp hc
      exact (dyadicGeneration_mem_iff G J c _).mpr
        ⟨by omega, ((dyadicFiniteTree_mem_iff G J c N).mp hcT).1⟩
    calc ∑ c ∈ (dyadicFiniteTree G J N).filter (fun c => c.1 = d), dyadicGridLength G c.1
        ≤ ∑ c ∈ dyadicGeneration G J (d - J.1).toNat, dyadicGridLength G c.1 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => (dyadicGridLength_pos G c.1).le
      _ = dyadicGridLength G J.1 := sum_dyadicGeneration_length G J _
  · have he : (dyadicFiniteTree G J N).filter (fun c => c.1 = d) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun c hc hcd => hd ?_
      have := dyadicGridCell_depth_le_of_subset G c J ((dyadicFiniteTree_mem_iff G J c N).mp hc).1
      omega
    rw [he, Finset.sum_empty]
    exact (dyadicGridLength_pos G J.1).le

/-! ### The base data of one tuple of the stagger expansion -/



end TrilinearHT.Auto
end
