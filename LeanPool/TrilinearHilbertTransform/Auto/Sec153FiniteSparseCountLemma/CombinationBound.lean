/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec153FiniteSparseCountLemma.TripleCountBound

/-!
# Trilinear Hilbert transform: combination_bound
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace SparseCountData
variable (D : SparseCountData)

open scoped Classical in
private def CombinationBoundStage1Statement : Prop :=
  ∀ (D : SparseCountData)
    (C : Finset (ℤ × (Fin (4 : ℕ) → ℤ)))
    (_ : ∀ o ∈ C, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1)
    (δ : ℝ)
    (_ : (0 : ℝ) < δ)
    (e : Fin (3 : ℕ) → Fin (4 : ℕ))
    (_ : ∀ (j : Fin (3 : ℕ)), e j ∈ D.core)
    (l : Fin (4 : ℕ))
    (B : Fin (3 : ℕ) → Finset ℤ)
    (P : Fin (3 : ℕ) → Finset ℤ)
    (ε : Fin (3 : ℕ) → ℕ)
    (N₀ : ℕ)
    (Rp : Fin (3 : ℕ) → ℝ)
    (_ : ∀ o ∈ C, ∀ (j : Fin (3 : ℕ)), o.2 (e j) ∈ B j)
    (_ : ∀ (j : Fin (3 : ℕ)), ∀ a ∈ B j, ∀ b ∈ B j, ∃ p ∈ P j, a - b - p ∈ shiftBox D.ζ N₀ (ε
      j) (2 : ℕ))
    (K₁ : ℝ)
    (_ : (0 : ℝ) ≤ K₁)
    (_ : ∀ (j : Fin (3 : ℕ)), (↑(P j).card : ℝ) ≤ K₁ * D.M)
    (_ : ∀ (j : Fin (3 : ℕ)), (↑(ε j) : ℝ) ≤ (17 : ℝ) * D.ν * Rp j)
    (_ : ∀ (j : Fin (3 : ℕ)), ∀ o ∈ C, Rp j < D.R o.1)
    (_ : (↑N₀ : ℝ) ≤ (33 : ℝ) * D.B)
    (g : ℕ)
    (_ : (612000000 : ℝ) * ((↑D.d : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * D.ν ≤ (2 : ℝ) ^ g * D.μ)
    (_ : (7200000 : ℝ) * ((↑D.d : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * D.B ≤ D.Q)
    (_ : (700000 : ℝ) * ((↑D.d : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * D.ν ≤ D.Sg)
    (_ : (↑C.card : ℝ) ≤ (↑D.L : ℝ) * D.M ^ (2 : ℕ))
    (_ : (0 : ℝ) < D.M)
    (_ : (1 : ℝ) ≤ (↑D.L : ℝ))
    (_ : (0 : ℝ) < D.μ)
    (_ : (0 : ℝ) < D.ν)
    (_ : (1 : ℝ) ≤ D.B)
    (_ : (1 : ℝ) ≤ ((↑D.d : ℝ) + (1 : ℝ)) ^ (2 : ℕ))
    (_ : (1 : ℝ) ≤ (↑g : ℝ))
    (_ : (0 : ℝ) < (↑C.card : ℝ))
    (c₁ : ℤ)
    (c₂ : ℤ)
    (_ : c₂ < c₁)
    (_ : ∀ (j : Fin (3 : ℕ)), |roleCoeff (e j) l| ≤ (3 : ℤ))
    (β : Fin (3 : ℕ) → ℤ)
    (_ : ∀ (j : Fin (3 : ℕ)), roleCoeff (e j) l * β j = (6 : ℤ)),
  let First : Finset (ℤ × (Fin (4 : ℕ) → ℤ)) :=
    {o ∈ C | c₁ ≤ o.1}
  let B₀ : Fin (3 : ℕ) → Finset ℤ :=
    fun (j : Fin (3 : ℕ)) => Finset.image (fun (o : ℤ × (Fin (4 : ℕ) → ℤ)) => o.2 (e j))
      First
  ∀ (_ : ∀ (j : Fin (3 : ℕ)), (↑C.card : ℝ) / D.M ^ (2 : ℕ) * D.M / ((3 : ℝ) * (↑D.L : ℝ)) ≤
      (↑(B₀ j).card : ℝ))
    (_ : ∀ (j : Fin (3 : ℕ)), B₀ j ⊆ B j)
    (_ : ∀ (j : Fin (3 : ℕ)), (B₀ j).Nonempty),
  let Last : Finset (ℤ × (Fin (4 : ℕ) → ℤ)) :=
    {o ∈ C | o.1 < c₂}
  let proj : ℤ × (Fin (4 : ℕ) → ℤ) → Fin (3 : ℕ) → ℤ :=
    fun (o : ℤ × (Fin (4 : ℕ) → ℤ)) (j : Fin (3 : ℕ)) => o.2 (e j)
  let F : Finset (Fin (3 : ℕ) → ℤ) :=
    Finset.image proj Last
  ∀ (_ : (↑C.card : ℝ) / D.M ^ (2 : ℕ) * D.M ^ (2 : ℕ) / ((4 : ℝ) * (↑D.L : ℝ)) ≤ (↑F.card :
      ℝ))
    (of : (Fin (3 : ℕ) → ℤ) → ℤ × (Fin (4 : ℕ) → ℤ))
    (_ : ∀ f ∈ F, of f ∈ Last)
    (_ : ∀ f ∈ F, proj (of f) = f)
    (_ : ∀ f ∈ F, of f ∈ C)
    (_ : ∀ f ∈ F, (of f).1 < c₂)
    (_ : ∀ f ∈ F, ∀ (j : Fin (3 : ℕ)), f j ∈ B j)
    (sF : ℤ)
    (_ : ∀ o ∈ Last, o.1 ≤ sF)
    (_ : ℤ × (Fin (4 : ℕ) → ℤ))
    (_ : sF < c₂)
    (_ : ∀ (j : Fin (3 : ℕ)), Rp j < D.R sF)
    (V : Finset ℤ)
    (_ : ∀ v ∈ V, sF + (↑g : ℤ) ≤ v)
    (_ : ∀ v ∈ V, ∀ v' ∈ V, v' < v → v' + (↑g : ℤ) ≤ v)
    (_ : (↑C.card : ℝ) / D.M ^ (2 : ℕ) / ((8 : ℝ) * (↑g : ℝ) * δ) ≤ (↑V.card : ℝ))
    (ov : ℤ → ℤ × (Fin (4 : ℕ) → ℤ))
    (_ : ∀ v ∈ V, (ov v).1 = v)
    (_ : ∀ v ∈ V, ov v ∈ C)
    (_ : ∀ v ∈ V, v < c₁)
    (nO : ℤ × (Fin (4 : ℕ) → ℤ) → Fin D.d → ℤ)
    (_ : ∀ o ∈ C, ∀ (r : Fin D.d), |(↑(nO o r) : ℝ)| ≤ D.B)
    (_ : ∀ o ∈ C, D.μ * D.R o.1 ≤ |(↑(tripleResidual D.ζ (fun (j : Fin (3 : ℕ)) => roleCoeff
      (e j) l) (proj o) (nO o)) : ℝ)|)
    (_ : ∀ o ∈ C, |(↑(tripleResidual D.ζ (fun (j : Fin (3 : ℕ)) => roleCoeff (e j) l) (proj
      o) (nO o)) : ℝ)| ≤ D.ν * D.R o.1)
    (kH : ℕ)
    (_ : (2 : ℕ) * kH + (1 : ℕ) ≤ (1000 : ℕ) * (D.d + (1 : ℕ)) ^ (2 : ℕ))
    (_ : ∀ (i : Fin (3 : ℕ)), (shiftBox D.ζ N₀ (ε i) ((2 : ℕ) * kH + (3 : ℕ))).card ≤ (2 : ℕ)
      * (shiftBox D.ζ N₀ (ε i) ((2 : ℕ) * kH + (1 : ℕ))).card),
  ((↑C.card : ℝ) / D.M ^ (2 : ℕ)) ^ (10 : ℕ) ≤ (10 : ℝ) ^ (6 : ℕ) * δ * (↑g : ℝ) * K₁
    ^ (7 : ℕ) * (↑D.L : ℝ) ^ (9 : ℕ)




private theorem combination_bound_stage_1 : CombinationBoundStage1Statement := by
  classical
  intro D C hC δ hδ e heC l B P ε N₀ Rp hBC hcov K₁ hK hP hε hRp hN₀ g hgΓ hQ hSg hCL hM0 hL hμ hν
    hB1 hd1 hgR hCR c₁ c₂ hc21 hα3 β hαβ First B₀ hB₀low hB₀sub hB₀ne Last proj F hFlow of hofL
    hofp hofC hofs hF sF hsF oF hsFc hRpF V hVsF hVsep hVlow ov hovs hovC hvc₁ nO hnO hnO1 hnO2 kH
    hkH hdbl
  have hdouble : ∀ j, (shiftBox D.ζ N₀ (ε j) (2 * kH + 1 + 2)).card ≤
      2 * (shiftBox D.ζ N₀ (ε j) (2 * kH + 1)).card := fun j => hdbl j
  have hH : ((2 * kH + 1 : ℕ) : ℝ) ≤ 1000 * ((D.d : ℝ) + 1) ^ 2 := by exact_mod_cast hkH
  have hH0 : (0 : ℝ) ≤ ((2 * kH + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSg0 : 0 ≤ D.Sg := le_trans (by positivity) hSg
  have hdν : 0 ≤ ((D.d : ℝ) + 1) ^ 2 * D.ν := by positivity
  have hRpnn : ∀ j, 0 ≤ Rp j := fun j => by
    have := hε j; have : (0 : ℝ) ≤ ε j := Nat.cast_nonneg _
    nlinarith
  have hεH : ∀ j, ((2 * kH + 1 : ℕ) : ℝ) * ε j ≤ 17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * Rp j := by
    intro j
    have h0 : (0 : ℝ) ≤ ε j := Nat.cast_nonneg _
    calc ((2 * kH + 1 : ℕ) : ℝ) * ε j ≤ 1000 * ((D.d : ℝ) + 1) ^ 2 * (17 * D.ν * Rp j) :=
          mul_le_mul hH (hε j) h0 (by positivity)
      _ = 17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * Rp j := by ring
  -- hypotheses of the slab count
  have hanch : ∀ j, ∀ a ∈ B₀ j, ∀ a' ∈ B₀ j, ∀ k : Fin D.d → ℤ, (∀ i, |(k i : ℝ)| ≤ D.Q) →
      |((a - a' - shiftDot k D.ζ : ℤ) : ℝ)| ≤ D.Sg * D.R c₁ → a = a' := by
    intro j a ha a' ha' kk hkk hle
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨o', ho', rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨hoC, hoc⟩ := Finset.mem_filter.mp ho
    obtain ⟨ho'C, -⟩ := Finset.mem_filter.mp ho'
    by_contra hne
    have := D.sep (e j) (heC j) o.1 (hC o hoC).1 o'.1 (hC o' ho'C).1 o.2 (hC o hoC).2 o'.2
      (hC o' ho'C).2 hne (-kk) (fun r => by simpa using hkk r)
    rw [shiftDot_neg, ← sub_eq_add_neg] at this
    have h1 : D.Sg * D.R c₁ ≤ D.Sg * max (D.R₀ * 2 ^ o.1) (D.R₀ * 2 ^ o'.1) :=
      mul_le_mul_of_nonneg_left ((D.R_strictMono.monotone hoc).trans (le_max_left _ _)) hSg0
    exact lt_irrefl _ ((hle.trans h1).trans_lt this)
  have hsepF : ∀ f ∈ F, ∀ f' ∈ F, ∀ j, ∀ k : Fin D.d → ℤ, (∀ i, |(k i : ℝ)| ≤ D.Q) →
      |((f j - f' j - shiftDot k D.ζ : ℤ) : ℝ)| ≤ 4 * (((2 * kH + 1 : ℕ) : ℝ) * ε j) →
        f j = f' j := by
    intro f hf f' hf' j kk hkk hle
    by_contra hne
    have hfj : (of f).2 (e j) = f j := congrFun (hofp f hf) j
    have hf'j : (of f').2 (e j) = f' j := congrFun (hofp f' hf') j
    have := D.sep (e j) (heC j) _ (hC _ (hofC f hf)).1 _ (hC _ (hofC f' hf')).1 _
      (hC _ (hofC f hf)).2 _ (hC _ (hofC f' hf')).2 (by rw [hfj, hf'j]; exact hne) (-kk)
      (fun r => by simpa using hkk r)
    rw [shiftDot_neg, ← sub_eq_add_neg, hfj, hf'j] at this
    have h1 : Rp j < D.R (of f).1 := hRp j _ (hofC f hf)
    have h2 : 4 * (((2 * kH + 1 : ℕ) : ℝ) * ε j) < D.Sg * D.R (of f).1 := by
      have h4 := hεH j
      have h5 : 17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * Rp j < 17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν *
          D.R (of f).1 := mul_lt_mul_of_pos_left h1 (by positivity)
      have h6 : 68000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * D.R (of f).1 ≤ D.Sg * D.R (of f).1 :=
        mul_le_mul_of_nonneg_right (by linarith only [hSg, hdν]) (D.R_pos _).le
      linarith only [h4, h5, h6]
    have h3 : D.Sg * D.R (of f).1 ≤ D.Sg * max (D.R₀ * 2 ^ (of f).1) (D.R₀ * 2 ^ (of f').1) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hSg0
    change D.Sg * D.R (of f).1 ≤ _ at h3
    exact lt_irrefl _ (((hle.trans h2.le).trans h3).trans_lt this)
  have h2g : ∀ a b : ℤ, a + g ≤ b → 2 ^ g * D.R a ≤ D.R b := by
    intro a b hab
    rw [← D.R_add]; exact D.R_strictMono.monotone hab
  have h1000 : 1000 * D.ν ≤ 2 ^ g * D.μ := by
    have : 1000 * D.ν ≤ 612000000 * ((D.d : ℝ) + 1) ^ 2 * D.ν := by
      nlinarith only [hd1, hν]
    linarith only [this, hgΓ]
  have hsmall : ∀ a b : ℤ, a + g ≤ b → ∀ c : ℝ, 0 ≤ c → 1000 * c ≤ 2 ^ g * D.μ →
      c * D.R a ≤ D.μ * D.R b / 1000 := by
    intro a b hab c hc hcg
    have h1 := h2g a b hab
    have hRa := (D.R_pos a).le
    rw [le_div_iff₀ (by norm_num)]
    calc c * D.R a * 1000 = (1000 * c) * D.R a := by ring
      _ ≤ (2 ^ g * D.μ) * D.R a := mul_le_mul_of_nonneg_right hcg hRa
      _ = D.μ * (2 ^ g * D.R a) := by ring
      _ ≤ D.μ * D.R b := mul_le_mul_of_nonneg_left h1 hμ.le
  have hsmallv : ∀ v ∈ V, ∀ v' ∈ V, D.R v' < D.R v → D.ν * D.R v' ≤ D.μ * D.R v / 1000 := by
    intro v hv v' hv' hlt
    exact hsmall v' v (hVsep v hv v' hv' (D.R_strictMono.lt_iff_lt.mp hlt)) D.ν hν.le h1000
  have hsmallf : ∀ v ∈ V, ∀ f ∈ F, D.ν * D.R (of f).1 ≤ D.μ * D.R v / 1000 := by
    intro v hv f hf
    have h1 : D.R (of f).1 ≤ D.R sF := D.R_strictMono.monotone (hsF _ (hofL f hf))
    exact (mul_le_mul_of_nonneg_left h1 hν.le).trans (hsmall sF v (hVsF v hv) D.ν hν.le h1000)
  have hsmallε : ∀ v ∈ V, ∀ j, 36 * (((2 * kH + 1 : ℕ) : ℝ) * ε j) ≤ D.μ * D.R v / 1000 := by
    intro v hv j
    have h1 := hεH j
    have h2 : Rp j ≤ D.R sF := (hRpF j).le
    have hc : 0 ≤ 612000 * ((D.d : ℝ) + 1) ^ 2 * D.ν := by positivity
    have h3 := hsmall sF v (hVsF v hv) _ hc (by linarith only [hgΓ])
    have h4 : 36 * (((2 * kH + 1 : ℕ) : ℝ) * ε j) ≤
        612000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * D.R sF := by
      have h5 : 17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * Rp j ≤
          17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * D.R sF :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith only [h1, h5]
    exact h4.trans h3
  have hgap : ∀ v ∈ V, ∀ m : Fin D.d → ℤ, (∀ i, |(m i : ℝ)| ≤ D.Q) →
      ¬ (D.μ * D.R v / 50 ≤ |(shiftDot m D.ζ : ℝ)| ∧
        |(shiftDot m D.ζ : ℝ)| ≤ 50 * D.ν * D.R v) := by
    intro v hv m hm
    have hvs := hovs v hv
    have hS := (hC _ (hovC v hv)).1
    have hE := (hC _ (hovC v hv)).2
    rw [hvs] at hS hE
    exact D.gap v hS ⟨_, hE⟩ m hm
  have hQ' : 144 * D.B + 216 * (((2 * kH + 1 : ℕ) : ℝ) * N₀) ≤ D.Q := by
    have h1 : ((2 * kH + 1 : ℕ) : ℝ) * N₀ ≤ 1000 * ((D.d : ℝ) + 1) ^ 2 * (33 * D.B) :=
      mul_le_mul hH hN₀ (Nat.cast_nonneg _) (by positivity)
    have h2 : D.B ≤ ((D.d : ℝ) + 1) ^ 2 * D.B := le_mul_of_one_le_left (by linarith) hd1
    have hpos : 0 ≤ ((D.d : ℝ) + 1) ^ 2 * D.B := by positivity
    linarith only [h1, h2, hQ, hpos]
  have hRc : ∀ j, Rp j ≤ D.R c₁ :=
    fun j => (hRpF j).le.trans (D.R_strictMono.monotone (by omega))
  have hS' : 12 * (((2 * kH + 1 : ℕ) : ℝ) * ((ε 0 : ℝ) + ε 1 + ε 2)) + 4 * D.ν * D.R c₁ ≤
      D.Sg * D.R c₁ := by
    have hj : ∀ j, ((2 * kH + 1 : ℕ) : ℝ) * ε j ≤ 17000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * D.R c₁ :=
      fun j => (hεH j).trans (mul_le_mul_of_nonneg_left (hRc j) (by positivity))
    have h1 := hj 0
    have h2 := hj 1
    have h3 := hj 2
    have hR := (D.R_pos c₁).le
    have h4 : 4 * D.ν * D.R c₁ ≤ 4 * (((D.d : ℝ) + 1) ^ 2 * D.ν) * D.R c₁ :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hd1, hν]) hR
    have h5 : 700000 * ((D.d : ℝ) + 1) ^ 2 * D.ν * D.R c₁ ≤ D.Sg * D.R c₁ :=
      mul_le_mul_of_nonneg_right hSg hR
    have e : 12 * (((2 * kH + 1 : ℕ) : ℝ) * ((ε 0 : ℝ) + ε 1 + ε 2)) =
        12 * (((2 * kH + 1 : ℕ) : ℝ) * ε 0) + 12 * (((2 * kH + 1 : ℕ) : ℝ) * ε 1) +
          12 * (((2 * kH + 1 : ℕ) : ℝ) * ε 2) := by ring
    rw [e]
    have hpos : 0 ≤ ((D.d : ℝ) + 1) ^ 2 * D.ν * D.R c₁ := by positivity
    nlinarith only [h1, h2, h3, h4, h5, hpos]
  have hRv : ∀ v ∈ V, D.R v ≤ D.R c₁ := fun v hv => D.R_strictMono.monotone (hvc₁ v hv).le
  have hRf : ∀ f ∈ F, D.R (of f).1 ≤ D.R c₁ :=
    fun f hf => D.R_strictMono.monotone (by have := hofs f hf; omega)
  have hcount := triple_count_bound D.ζ N₀ (2 * kH + 1) ε (fun j => roleCoeff (e j) l) β hαβ hα3
    B B₀ P hB₀sub hB₀ne hcov hdouble (Q := D.Q) (S := D.Sg * D.R c₁) (μ := D.μ) (ν := D.ν)
    (Rs := D.R c₁) (Bw := D.B) (D.R_pos c₁).le hν.le (by linarith only [hB1]) hanch V
    (fun v => proj (ov v)) (fun v hv j => hBC _ (hovC v hv) j) D.R F hF (fun f => D.R (of f).1)
    (fun v => nO (ov v)) (fun f => nO (of f)) (fun v hv => hnO _ (hovC v hv))
    (fun f hf => hnO _ (hofC f hf))
    (fun v hv => by
      have h1 := hnO1 _ (hovC v hv); have h2 := hnO2 _ (hovC v hv)
      rw [hovs v hv] at h1 h2; exact ⟨h1, h2⟩)
    (fun f hf => by have h := hnO2 _ (hofC f hf); rwa [hofp f hf] at h) hRv hRf hsepF
    (fun v _ v' _ hne => (lt_or_gt_of_ne (fun h => hne (D.R_strictMono.injective h.symm))))
    hsmallv hsmallf hsmallε hgap hQ' hS' (fun v _ => (mul_pos hμ (D.R_pos v)).le)
  have hcountR : (V.card : ℝ) * F.card ≤
      ((2 * ((P 0).card : ℝ) / (B₀ 0).card) ^ 2 * (B₀ 0).card) *
        ((2 * ((P 1).card : ℝ) / (B₀ 1).card) ^ 2 * (B₀ 1).card) *
          (2 * ((P 2).card : ℝ) / (B₀ 2).card) ^ 3 := by
    have := (Rat.cast_le (K := ℝ)).mpr hcount
    push_cast at this
    exact this
  have hρ : (0 : ℝ) < C.card / D.M ^ 2 := div_pos hCR (pow_pos hM0 2)
  exact combination_arith hρ hM0 hL hδ hgR hK (hB₀low 0) (hB₀low 1) (hB₀low 2)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hP 0) (hP 1) (hP 2) hVlow hFlow
    hcountR (by rw [div_le_iff₀ (pow_pos hM0 2)]; exact hCL)


/-- Blueprint lines 2640-2698 (one combination): occurrences of one block whose three future
roles lie in fixed future cover subsets `B_j` (with difference covers of size at most `K₁ M`
relative to the future block widths) have normalized mass `ρ = |C|/M²` with
`ρ ≤ 12 g δ` or `ρ¹⁰ ≤ 10⁶ δ g K₁⁷ L⁹`, where `2^g` exceeds the margin `Γ`. -/
theorem combination_bound (C : Finset (ℤ × (Fin 4 → ℤ)))
    (hC : ∀ o ∈ C, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) {δ : ℝ} (hδ : 0 < δ)
    (hδm : ∀ s, ((C.filter fun o => o.1 = s).card : ℝ) ≤ δ * D.M ^ 2)
    (e : Fin 3 → Fin 4) (he : Function.Injective e) (heC : ∀ j, e j ∈ D.core) {l : Fin 4}
    (hl : ∀ j, e j ≠ l) (B P : Fin 3 → Finset ℤ) (ε : Fin 3 → ℕ) (N₀ : ℕ) (Rp : Fin 3 → ℝ)
    (hBC : ∀ o ∈ C, ∀ j, o.2 (e j) ∈ B j)
    (hcov : ∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∃ p ∈ P j, a - b - p ∈ shiftBox D.ζ N₀ (ε j) 2)
    {K₁ : ℝ} (hK : 0 ≤ K₁) (hP : ∀ j, ((P j).card : ℝ) ≤ K₁ * D.M)
    (hε : ∀ j, (ε j : ℝ) ≤ 17 * D.ν * Rp j) (hRp : ∀ j, ∀ o ∈ C, Rp j < D.R o.1)
    (hN₀ : (N₀ : ℝ) ≤ 33 * D.B) {g : ℕ} (hg : 1 ≤ g)
    (hgΓ : 612000000 * ((D.d : ℝ) + 1) ^ 2 * D.ν ≤ 2 ^ g * D.μ)
    (hQ : 7200000 * ((D.d : ℝ) + 1) ^ 2 * D.B ≤ D.Q)
    (hSg : 700000 * ((D.d : ℝ) + 1) ^ 2 * D.ν ≤ D.Sg)
    (hbig : 12 * g * δ * D.M ^ 2 < C.card) (hCL : (C.card : ℝ) ≤ D.L * D.M ^ 2) :
    ((C.card : ℝ) / D.M ^ 2) ^ 10 ≤ 10 ^ 6 * δ * g * K₁ ^ 7 * D.L ^ 9 := by
  classical
  have hM := D.one_le_M
  have hM0 : 0 < D.M := by linarith
  have hL : (1 : ℝ) ≤ D.L := by exact_mod_cast D.one_le_L
  have hμ := D.μ_pos
  have hν : 0 < D.ν := lt_of_lt_of_le hμ D.μ_le_ν
  have hB1 := D.one_le_B
  have hd1 : (1 : ℝ) ≤ ((D.d : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ D.d := Nat.cast_nonneg _
    nlinarith only [this]
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hCR : (0 : ℝ) < C.card := lt_of_le_of_lt (by positivity) hbig
  have hCpos : 0 < C.card := by exact_mod_cast hCR
  have h12 : 12 * (δ * D.M ^ 2) ≤ C.card := by nlinarith only [mul_pos hδ (pow_pos hM0 2), hbig,
      hgR]
  obtain ⟨c₁, c₂, hc21, hfirst, hmiddle, hlast⟩ := mass_ranges C hδm h12 hCpos
  -- the triple coefficients
  have hα : ∀ j, |roleCoeff (e j) l| ≤ 3 ∧ ∃ β : ℤ, roleCoeff (e j) l * β = 6 :=
    fun j => roleCoeff_spec (hl j)
  choose hα3 β hαβ using hα
  -- anchors
  set First := C.filter fun o => c₁ ≤ o.1
  set! B₀ : Fin 3 → Finset ℤ := fun j => First.image fun o => o.2 (e j)
  have hFirstC : ∀ o ∈ First, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 :=
    fun o ho => hC o (Finset.mem_filter.mp ho).1
  have hB₀low : ∀ j, (C.card : ℝ) / D.M ^ 2 * D.M / (3 * D.L) ≤ (B₀ j).card := by
    intro j
    have h1 := card_le_mul_card_image_real First (fun o => o.2 (e j)) (D.L * D.M) fun a _ =>
      le_trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.filter_subset _ _)))) (D.label_fiber_le C hC (heC j) a)
    have h2 : (C.card : ℝ) / 3 ≤ D.L * D.M * (B₀ j).card := hfirst.trans h1
    rw [div_le_iff₀ (by positivity)]
    have e : (C.card : ℝ) / D.M ^ 2 * D.M = C.card / D.M := by field_simp
    rw [e, div_le_iff₀ hM0]
    nlinarith only [hfirst, h1]
  have hB₀sub : ∀ j, B₀ j ⊆ B j := by
    intro j a ha
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp ha
    exact hBC o (Finset.mem_filter.mp ho).1 j
  have hB₀ne : ∀ j, (B₀ j).Nonempty := by
    intro j
    rw [← Finset.card_pos]
    have := hB₀low j
    have : (0 : ℝ) < (B₀ j).card := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  -- the last range
  set Last := C.filter fun o => o.1 < c₂
  set! proj : ℤ × (Fin 4 → ℤ) → Fin 3 → ℤ := fun o j => o.2 (e j)
  set! F := Last.image proj
  have hLastC : ∀ o ∈ Last, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 :=
    fun o ho => hC o (Finset.mem_filter.mp ho).1
  have hFlow : (C.card : ℝ) / D.M ^ 2 * D.M ^ 2 / (4 * D.L) ≤ F.card := by
    have h1 := card_le_mul_card_image_real Last proj D.L fun f _ =>
      by exact_mod_cast D.proj_fiber_le Last hLastC e he heC f
    have e : (C.card : ℝ) / D.M ^ 2 * D.M ^ 2 = C.card := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith only [hlast, h1]
  have hFwit : ∀ f ∈ F, ∃ o ∈ Last, proj o = f := fun f hf => Finset.mem_image.mp hf
  choose! of hofL hofp using hFwit
  have hofC : ∀ f ∈ F, of f ∈ C := fun f hf => (Finset.mem_filter.mp (hofL f hf)).1
  have hofs : ∀ f ∈ F, (of f).1 < c₂ := fun f hf => (Finset.mem_filter.mp (hofL f hf)).2
  have hF : ∀ f ∈ F, ∀ j, f j ∈ B j := by
    intro f hf j
    rw [← hofp f hf]
    exact hBC _ (hofC f hf) j
  -- the largest last-range scale
  have hLastne : Last.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Last.card := lt_of_lt_of_le (by positivity) hlast
    exact_mod_cast this
  obtain ⟨sF, hsFmem, hsFmax⟩ : ∃ sF ∈ Last.image Prod.fst, ∀ s ∈ Last.image Prod.fst,
      s ≤ sF := ⟨_, Finset.max'_mem _ (hLastne.image _), fun s hs => Finset.le_max' _ _ hs⟩
  have hsF : ∀ o ∈ Last, o.1 ≤ sF := fun o ho => hsFmax _ (Finset.mem_image_of_mem _ ho)
  obtain ⟨oF, hoF, hoFs⟩ := Finset.mem_image.mp hsFmem
  have hsFc : sF < c₂ := by rw [← hoFs]; exact (Finset.mem_filter.mp hoF).2
  have hRpF : ∀ j, Rp j < D.R sF := by
    intro j
    have := hRp j oF (Finset.mem_filter.mp hoF).1
    rwa [hoFs] at this
  -- the middle range and the selected scales
  set Mid := C.filter fun o => c₂ ≤ o.1 ∧ o.1 < c₁
  set! Wm := Mid.image Prod.fst
  have hWmlow : (C.card : ℝ) / 4 ≤ δ * D.M ^ 2 * Wm.card := by
    refine hmiddle.trans (card_le_mul_card_image_real Mid Prod.fst _ fun s _ => ?_)
    exact le_trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.filter_subset _ _)))) (hδm s)
  have hWm : ∀ s ∈ Wm, sF < s := by
    intro s hs
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hs
    exact lt_of_lt_of_le hsFc (Finset.mem_filter.mp ho).2.1
  obtain ⟨V, hVW, hVsF, hVsep, hVcard⟩ := residue_selection Wm sF hWm hg
  have hVlow : (C.card : ℝ) / D.M ^ 2 / (8 * g * δ) ≤ V.card := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have h1 : δ * D.M ^ 2 * Wm.card ≤ δ * D.M ^ 2 * (g * V.card + g) :=
      mul_le_mul_of_nonneg_left hVcard (by positivity)
    linarith
  have hVwit : ∀ v ∈ V, ∃ o ∈ Mid, o.1 = v := fun v hv => Finset.mem_image.mp (hVW hv)
  choose! ov hovM hovs using hVwit
  have hovC : ∀ v ∈ V, ov v ∈ C := fun v hv => (Finset.mem_filter.mp (hovM v hv)).1
  have hvc₁ : ∀ v ∈ V, v < c₁ := by
    intro v hv; rw [← hovs v hv]; exact (Finset.mem_filter.mp (hovM v hv)).2.2
  -- annular witnesses
  have hannO : ∀ o ∈ C, ∃ n : Fin D.d → ℤ, (∀ r, |(n r : ℝ)| ≤ D.B) ∧
      D.μ * D.R o.1 ≤ |(tripleResidual D.ζ (fun j => roleCoeff (e j) l) (proj o) n : ℝ)| ∧
      |(tripleResidual D.ζ (fun j => roleCoeff (e j) l) (proj o) n : ℝ)| ≤ D.ν * D.R o.1 :=
    fun o ho => D.ann_triple e he heC hl (hC o ho).1 (hC o ho).2
  choose! nO hnO hnO1 hnO2 using hannO
  -- the small-growth scale
  obtain ⟨kH, hkH, hdbl⟩ := exists_small_growth_scale (fun j t => shiftBox D.ζ N₀ (ε j) t)
    (D := D.d + 1) (by omega) (fun j t t' h => shiftBox_mono _ _ _ h)
    (fun j => ⟨0, zero_mem_shiftBox _ _ _ _⟩) (fun j t => card_shiftBox_le _ _ _ _)
  expose_names
  exact @combination_bound_stage_1 D C hC δ hδ e heC l B P ε N₀ Rp hBC hcov K₁ hK hP hε hRp hN₀ g
    hgΓ hQ hSg hCL hM0 hL hμ hν hB1 hd1 hgR hCR c₁ c₂ hc21 hα3 β hαβ hB₀low hB₀sub hB₀ne hFlow of
    hofL hofp hofC hofs hF sF hsF oF hsFc hRpF V hVsF hVsep hVlow ov hovs hovC hvc₁ nO hnO hnO1
    hnO2 kH hkH hdbl

end SparseCountData

section CountingBlocks
variable {α : Type*}

/-! ### Counting blocks (lem:sparse-count, blueprint lines 2613-2616) -/

/-- The counting block of scale `s`: `⌊G(s)/θ⌋` for the mass `G(s)` of scales `≥ s`. -/
noncomputable def blockIndex (C : Finset (ℤ × α)) (θ : ℝ) (s : ℤ) : ℕ :=
  ⌊(upperMass C s : ℝ) / θ⌋₊

theorem upperMass_anti (C : Finset (ℤ × α)) {s s' : ℤ} (h : s ≤ s') :
    upperMass C s' ≤ upperMass C s :=
  Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h' => le_trans h h')

/-- Larger scales lie in earlier (or equal) blocks. -/
theorem blockIndex_anti (C : Finset (ℤ × α)) {θ : ℝ} (hθ : 0 < θ) {s s' : ℤ} (h : s ≤ s') :
    blockIndex C θ s' ≤ blockIndex C θ s := by
  unfold blockIndex
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by exact_mod_cast upperMass_anti C h)
    hθ.le)

/-- A later block consists of strictly smaller scales. -/
theorem lt_of_blockIndex_lt (C : Finset (ℤ × α)) {θ : ℝ} (hθ : 0 < θ) {s s' : ℤ}
    (h : blockIndex C θ s < blockIndex C θ s') : s' < s := by
  by_contra h'
  push Not at h'
  exact absurd (blockIndex_anti C hθ h') (not_le.mpr h)

theorem blockIndex_lt (C : Finset (ℤ × α)) {θ : ℝ} (hθ : 0 < θ) (s : ℤ) :
    blockIndex C θ s < ⌊(C.card : ℝ) / θ⌋₊ + 1 := by
  unfold blockIndex
  refine Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ hθ.le))
  exact_mod_cast Finset.card_filter_le _ _

/-- Blueprint lines 2614-2615: each counting block has mass at most `θ + m₀`, where `m₀` bounds
the mass of a single scale. -/
theorem block_mass_le (C : Finset (ℤ × α)) {θ m₀ : ℝ} (hθ : 0 < θ)
    (hm : ∀ s, ((C.filter fun o => o.1 = s).card : ℝ) ≤ m₀) (b : ℕ) :
    ((C.filter fun o => blockIndex C θ o.1 = b).card : ℝ) ≤ θ + m₀ := by
  classical
  set Cb := C.filter fun o => blockIndex C θ o.1 = b
  rcases Cb.eq_empty_or_nonempty with h | hne
  · rw [h, Finset.card_empty, Nat.cast_zero]
    have := (Nat.cast_nonneg _).trans (hm 0)
    linarith
  obtain ⟨slo, hslo, hslomin⟩ : ∃ s ∈ Cb.image Prod.fst, ∀ t ∈ Cb.image Prod.fst, s ≤ t :=
    ⟨_, Finset.min'_mem _ (hne.image _), fun t ht => Finset.min'_le _ _ ht⟩
  obtain ⟨shi, hshi, hshimax⟩ : ∃ s ∈ Cb.image Prod.fst, ∀ t ∈ Cb.image Prod.fst, t ≤ s :=
    ⟨_, Finset.max'_mem _ (hne.image _), fun t ht => Finset.le_max' _ _ ht⟩
  obtain ⟨olo, holo, rfl⟩ := Finset.mem_image.mp hslo
  obtain ⟨ohi, hohi, rfl⟩ := Finset.mem_image.mp hshi
  have hblo := (Finset.mem_filter.mp holo).2
  have hbhi := (Finset.mem_filter.mp hohi).2
  -- `G(s_lo) < (b+1)θ` and `bθ ≤ G(s_hi)`
  have h1 : (upperMass C olo.1 : ℝ) < (b + 1) * θ := by
    have := Nat.lt_floor_add_one ((upperMass C olo.1 : ℝ) / θ)
    unfold blockIndex at hblo
    rw [hblo, div_lt_iff₀ hθ] at this
    exact_mod_cast this
  have h2 : (b : ℝ) * θ ≤ upperMass C ohi.1 := by
    have h := Nat.floor_le (div_nonneg (Nat.cast_nonneg (upperMass C ohi.1)) hθ.le)
    unfold blockIndex at hbhi
    rw [hbhi, le_div_iff₀ hθ] at h
    exact h
  -- the block lies between `s_lo` and `s_hi`
  have hsub : Cb ⊆ (C.filter fun o => o.1 = ohi.1) ∪
      ((C.filter fun o => olo.1 ≤ o.1) \ (C.filter fun o => ohi.1 ≤ o.1)) := by
    intro o ho
    have hoC := (Finset.mem_filter.mp ho).1
    have hlo := hslomin _ (Finset.mem_image_of_mem _ ho)
    have hhi := hshimax _ (Finset.mem_image_of_mem _ ho)
    rcases eq_or_lt_of_le hhi with heq | hlt
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hoC, heq⟩)
    · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hoC, hlo⟩,
        fun h => ?_⟩)
      exact absurd (Finset.mem_filter.mp h).2 (not_le.mpr hlt)
  have hsd : ((C.filter fun o => olo.1 ≤ o.1) \ (C.filter fun o => ohi.1 ≤ o.1)).card =
      upperMass C olo.1 - upperMass C ohi.1 := by
    rw [Finset.card_sdiff_of_subset (Finset.monotone_filter_right _ fun o _ h =>
      le_trans (hslomin _ (Finset.mem_image_of_mem _ hohi)) h)]
    rfl
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hsd] at hle
  have hle' : (Cb.card : ℝ) ≤ (C.filter fun o => o.1 = ohi.1).card +
      ((upperMass C olo.1 : ℝ) - upperMass C ohi.1) := by
    have hmono : upperMass C ohi.1 ≤ upperMass C olo.1 :=
      upperMass_anti C (hslomin _ (Finset.mem_image_of_mem _ hohi))
    have : ((upperMass C olo.1 - upperMass C ohi.1 : ℕ) : ℝ) =
        (upperMass C olo.1 : ℝ) - upperMass C ohi.1 := by
      rw [Nat.cast_sub hmono]
    rw [← this]; exact_mod_cast hle
  have := hm ohi.1
  nlinarith only [h1, h2, hle', this]

end CountingBlocks

/-- Blueprint lines 2628-2633 (nonfuture pairs): if the block masses satisfy
`mass_b ≤ min(c, L m_b m'_b)` and `Σ_b m_b, Σ_b m'_b ≤ M`, then `Σ_b mass_b ≤ √(c L) M`. -/
theorem nonfuture_pair_sum {ι : Type*} (J : Finset ι) (m m' mass : ι → ℝ)
    (hm : ∀ b ∈ J, 0 ≤ m b) (hm' : ∀ b ∈ J, 0 ≤ m' b) (hmass0 : ∀ b ∈ J, 0 ≤ mass b)
    {c L M : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (hmc : ∀ b ∈ J, mass b ≤ c)
    (hmL : ∀ b ∈ J, mass b ≤ L * m b * m' b) (hsum : ∑ b ∈ J, m b ≤ M)
    (hsum' : ∑ b ∈ J, m' b ≤ M) : ∑ b ∈ J, mass b ≤ Real.sqrt (c * L) * M := by
  have hpt : ∀ b ∈ J, mass b ≤ Real.sqrt (c * L) * Real.sqrt (m b * m' b) := by
    intro b hb
    rw [← Real.sqrt_mul (mul_nonneg hc hL)]
    refine Real.le_sqrt_of_sq_le ?_
    have h1 := hmc b hb
    have h2 := hmL b hb
    have h0 := hmass0 b hb
    calc mass b ^ 2 = mass b * mass b := by ring
      _ ≤ c * (L * m b * m' b) := mul_le_mul h1 h2 h0 hc
      _ = c * L * (m b * m' b) := by ring
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg hm) hsum
  calc ∑ b ∈ J, mass b ≤ ∑ b ∈ J, Real.sqrt (c * L) * Real.sqrt (m b * m' b) :=
        Finset.sum_le_sum hpt
    _ = Real.sqrt (c * L) * ∑ b ∈ J, Real.sqrt (m b * m' b) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (c * L) * (Real.sqrt (∑ b ∈ J, m b) * Real.sqrt (∑ b ∈ J, m' b)) :=
        mul_le_mul_of_nonneg_left (hull_maxima_cauchy_schwarz J m m' hm hm')
          (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (c * L) * (Real.sqrt M * Real.sqrt M) := by
        gcongr
    _ = Real.sqrt (c * L) * M := by rw [Real.mul_self_sqrt hM0]

/-- Disjoint subsets of a set of size at most `M` have total size at most `M`. -/
theorem sum_card_disjoint_le {ι : Type*} (J : Finset ι) (X : ι → Finset ℤ) (A : Finset ℤ)
    (hX : ∀ b ∈ J, X b ⊆ A) (hdis : ∀ b ∈ J, ∀ b' ∈ J, b ≠ b' → Disjoint (X b) (X b')) {M : ℝ}
    (hA : (A.card : ℝ) ≤ M) : ∑ b ∈ J, ((X b).card : ℝ) ≤ M := by
  classical
  have h1 : (J.biUnion X).card = ∑ b ∈ J, (X b).card :=
    Finset.card_biUnion fun b hb b' hb' hne => hdis b hb b' hb' hne
  have h2 := Finset.card_le_card (Finset.biUnion_subset.mpr hX)
  rw [h1] at h2
  push_cast [← Nat.cast_sum]
  exact (by exact_mod_cast h2 : ((∑ b ∈ J, (X b).card : ℕ) : ℝ) ≤ A.card).trans hA

namespace SparseCountData
variable (D : SparseCountData)

/-- Blueprint line 2627 (uncovered occurrences): occurrences missing an own-block covered label
in some core role have mass at most `J₀ · |core| · c` if each block and role contributes `≤ c`. -/
theorem uncovered_mass_le (Occ : Finset (ℤ × (Fin 4 → ℤ))) (β : ℤ → ℕ) (J₀ : ℕ)
    (hβ : ∀ o ∈ Occ, β o.1 < J₀) (𝓑 : ℕ → Fin 4 → Finset (Finset ℤ)) {c : ℝ}
    (hc : ∀ b < J₀, ∀ i ∈ D.core, (((Occ.filter fun o : ℤ × (Fin 4 → ℤ) => β o.1 = b).filter
      fun o : ℤ × (Fin 4 → ℤ) => ∀ B ∈ 𝓑 b i, o.2 i ∉ B).card : ℝ) ≤ c) :
    ((Occ.filter fun o : ℤ × (Fin 4 → ℤ) => ∃ i ∈ D.core, ∀ B ∈ 𝓑 (β o.1) i, o.2 i ∉ B).card : ℝ) ≤
      J₀ * D.core.card * c := by
  have hsub : (Occ.filter fun o : ℤ × (Fin 4 → ℤ) => ∃ i ∈ D.core, ∀ B ∈ 𝓑 (β o.1) i, o.2 i ∉ B) ⊆
      (Finset.range J₀).biUnion fun b => D.core.biUnion fun i =>
        (Occ.filter fun o => β o.1 = b).filter fun o => ∀ B ∈ 𝓑 b i, o.2 i ∉ B := by
    intro o ho
    obtain ⟨hoO, i, hi, hB⟩ := Finset.mem_filter.mp ho
    exact Finset.mem_biUnion.mpr ⟨β o.1, Finset.mem_range.mpr (hβ o hoO),
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hoO, rfl⟩,
        hB⟩⟩⟩
  refine (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans ?_
  push_cast
  calc ∑ b ∈ Finset.range J₀, ((D.core.biUnion fun i => (Occ.filter fun o => β o.1 = b).filter
        fun o => ∀ B ∈ 𝓑 b i, o.2 i ∉ B).card : ℝ)
      ≤ ∑ _b ∈ Finset.range J₀, (D.core.card * c) := by
        refine Finset.sum_le_sum fun b hb => ?_
        refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
        push_cast
        calc ∑ i ∈ D.core, (((Occ.filter fun o => β o.1 = b).filter
              fun o => ∀ B ∈ 𝓑 b i, o.2 i ∉ B).card : ℝ) ≤ ∑ _i ∈ D.core, c :=
              Finset.sum_le_sum fun i hi => hc b (Finset.mem_range.mp hb) i hi
          _ = D.core.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = J₀ * D.core.card * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Blueprint lines 2628-2633 (two nonfuture core roles): occurrences whose labels in two
distinct core roles are nonfuture labels of their block have mass at most `√(c L) M`, when each
block has mass at most `c`. -/
theorem pair_nonfuture_mass_le (Occ : Finset (ℤ × (Fin 4 → ℤ)))
    (hOcc : ∀ o ∈ Occ, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) (β : ℤ → ℕ) (J₀ : ℕ)
    (hβ : ∀ o ∈ Occ, β o.1 < J₀) (NF : ℕ → Fin 4 → Finset ℤ) {i j : Fin 4} (hi : i ∈ D.core)
    (hj : j ∈ D.core) (hij : i ≠ j) (hNFA : ∀ b, ∀ r ∈ D.core, NF b r ⊆ D.A r)
    (hNFdis : ∀ r ∈ D.core, ∀ b ∈ Finset.range J₀, ∀ b' ∈ Finset.range J₀, b ≠ b' →
      Disjoint (NF b r) (NF b' r)) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ b, ((Occ.filter fun o => β o.1 = b).card : ℝ) ≤ c) :
    ((Occ.filter fun o => o.2 i ∈ NF (β o.1) i ∧ o.2 j ∈ NF (β o.1) j).card : ℝ) ≤
      Real.sqrt (c * D.L) * D.M := by
  set Pij := Occ.filter fun o => o.2 i ∈ NF (β o.1) i ∧ o.2 j ∈ NF (β o.1) j
  have hPO : ∀ o ∈ Pij, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 := fun o ho => hOcc o (Finset.mem_filter.mp ho).1
  have hdecomp : (Pij.card : ℝ) = ∑ b ∈ Finset.range J₀,
      ((Pij.filter fun o => β o.1 = b).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun o => β o.1) (t := Finset.range J₀)
      fun o ho => Finset.mem_range.mpr (hβ o (Finset.mem_filter.mp ho).1)]
    push_cast; rfl
  rw [hdecomp]
  refine nonfuture_pair_sum (Finset.range J₀) (fun b => ((NF b i).card : ℝ))
    (fun b => ((NF b j).card : ℝ)) _ (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (fun _ _ => Nat.cast_nonneg _) hc (by exact_mod_cast (Nat.zero_le D.L)) ?_ ?_ ?_ ?_
  · intro b _
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun o ho => ?_)) (hblock b)
    obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ho1).1, ho2⟩
  · intro b _
    set Pb := Pij.filter fun o => β o.1 = b
    have hPb : ∀ o ∈ Pb, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 :=
      fun o ho => hPO o (Finset.mem_filter.mp ho).1
    have h1 := card_le_mul_card_image_real Pb (fun o => (o.2 i, o.2 j)) D.L fun e _ =>
      by exact_mod_cast D.pair_fiber_le Pb hPb hi hj hij e
    have h2 : (Pb.image fun o => (o.2 i, o.2 j)) ⊆ NF b i ×ˢ NF b j := by
      intro e he
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
      obtain ⟨-, hoi, hoj⟩ := Finset.mem_filter.mp ho1
      rw [ho2] at hoi hoj
      exact Finset.mem_product.mpr ⟨hoi, hoj⟩
    have h3 := Finset.card_le_card h2
    rw [Finset.card_product] at h3
    calc (Pb.card : ℝ) ≤ D.L * (Pb.image fun o => (o.2 i, o.2 j)).card := h1
      _ ≤ D.L * ((NF b i).card * (NF b j).card) := by
          gcongr; exact_mod_cast h3
      _ = D.L * (NF b i).card * (NF b j).card := by ring
  · exact sum_card_disjoint_le _ _ (D.A i) (fun b _ => hNFA b i hi) (hNFdis i hi) (D.card_A i hi)
  · exact sum_card_disjoint_le _ _ (D.A j) (fun b _ => hNFA b j hj) (hNFdis j hj) (D.card_A j hj)

/-- Blueprint lines 2628-2633 (a nonfuture core role and the side role, three cores): the side
incidence `w_s` gives `mass_b ≤ m_b Σ_{s ∈ b} w_s`, so these occurrences have mass at most
`√c M` when each block has mass at most `c`. -/
theorem side_nonfuture_mass_le (h3 : D.core.card = 3) (Occ : Finset (ℤ × (Fin 4 → ℤ)))
    (hOcc : ∀ o ∈ Occ, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) (β : ℤ → ℕ) (J₀ : ℕ)
    (hβ : ∀ o ∈ Occ, β o.1 < J₀) (NF : ℕ → Fin 4 → Finset ℤ) {i : Fin 4} (hi : i ∈ D.core)
    (hNFA : ∀ b, NF b i ⊆ D.A i)
    (hNFdis : ∀ b ∈ Finset.range J₀, ∀ b' ∈ Finset.range J₀, b ≠ b' →
      Disjoint (NF b i) (NF b' i)) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ b, ((Occ.filter fun o => β o.1 = b).card : ℝ) ≤ c) :
    ((Occ.filter fun o => o.2 i ∈ NF (β o.1) i).card : ℝ) ≤ Real.sqrt (c * 1) * D.M := by
  set P := Occ.filter fun o => o.2 i ∈ NF (β o.1) i
  set W : ℕ → ℝ := fun b => ∑ s ∈ (Occ.filter fun o => β o.1 = b).image Prod.fst, D.w s
  have hdecomp : (P.card : ℝ) =
      ∑ b ∈ Finset.range J₀, ((P.filter fun o => β o.1 = b).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun o => β o.1) (t := Finset.range J₀)
      fun o ho => Finset.mem_range.mpr (hβ o (Finset.mem_filter.mp ho).1)]
    push_cast; rfl
  rw [hdecomp]
  refine nonfuture_pair_sum (Finset.range J₀) (fun b => ((NF b i).card : ℝ)) W _
    (fun _ _ => Nat.cast_nonneg _) (fun b _ => Finset.sum_nonneg fun s _ => D.w_nonneg s)
    (fun _ _ => Nat.cast_nonneg _) hc zero_le_one ?_ ?_ ?_ ?_
  · intro b _
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun o ho => ?_)) (hblock b)
    obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ho1).1, ho2⟩
  · intro b _
    set Pb := P.filter fun o => β o.1 = b
    have hPbs : ∀ o ∈ Pb, o.1 ∈ (Occ.filter fun o => β o.1 = b).image Prod.fst := by
      intro o ho
      obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ho1).1, ho2⟩)
    rw [Finset.card_eq_sum_card_fiberwise hPbs]
    push_cast
    rw [one_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    obtain ⟨o₀, ho₀, rfl⟩ := Finset.mem_image.mp hs
    have hS := (hOcc o₀ (Finset.mem_filter.mp ho₀).1).1
    -- occurrences at scale `s` inject into tuples with a nonfuture `i`-label
    have h1 : (Pb.filter fun o => o.1 = o₀.1).card ≤
        ((D.E o₀.1).filter fun x => x i ∈ NF b i).card := by
      refine Finset.card_le_card_of_injOn (fun o => o.2) ?_ ?_
      · intro o ho
        obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
        obtain ⟨ho3, ho4⟩ := Finset.mem_filter.mp ho1
        obtain ⟨ho5, ho6⟩ := Finset.mem_filter.mp ho3
        have hx := (hOcc o ho5).2
        rw [ho2] at hx
        rw [ho4] at ho6
        exact Finset.mem_filter.mpr ⟨hx, ho6⟩
      · intro o ho o' ho' h
        have e1 := (Finset.mem_filter.mp ho).2
        have e2 := (Finset.mem_filter.mp ho').2
        exact Prod.ext (e1.trans e2.symm) h
    have h2 : (((D.E o₀.1).filter fun x => x i ∈ NF b i).card : ℝ) ≤
        (NF b i).card * D.w o₀.1 := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin 4 → ℤ => x i) (t := NF b i)
        (s := (D.E o₀.1).filter fun x => x i ∈ NF b i) fun x hx => (Finset.mem_filter.mp hx).2]
      push_cast
      calc ∑ a ∈ NF b i, ((((D.E o₀.1).filter fun x => x i ∈ NF b i).filter
            fun x => x i = a).card : ℝ) ≤ ∑ _a ∈ NF b i, D.w o₀.1 := by
            refine Finset.sum_le_sum fun a _ => ?_
            refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
              (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))) ?_
            exact D.w_inc h3 _ hS i hi a
        _ = (NF b i).card * D.w o₀.1 := by rw [Finset.sum_const, nsmul_eq_mul]
    exact (Nat.cast_le.mpr h1).trans h2
  · exact sum_card_disjoint_le _ _ (D.A i) (fun b _ => hNFA b) hNFdis (D.card_A i hi)
  · -- the side weights summed over blocks
    have hsub : ∀ b ∈ Finset.range J₀, (Occ.filter fun o => β o.1 = b).image Prod.fst ⊆
        (Occ.image Prod.fst).filter fun s => β s = b := by
      intro b _ s hs
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ho1, ho2⟩
    calc ∑ b ∈ Finset.range J₀, W b
        ≤ ∑ b ∈ Finset.range J₀, ∑ s ∈ (Occ.image Prod.fst).filter (fun s => β s = b), D.w s :=
          Finset.sum_le_sum fun b hb => Finset.sum_le_sum_of_subset_of_nonneg (hsub b hb)
            fun s _ _ => D.w_nonneg s
      _ = ∑ s ∈ Occ.image Prod.fst, D.w s := by
          rw [Finset.sum_fiberwise_of_maps_to (g := β) fun s hs => by
            obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hs
            exact Finset.mem_range.mpr (hβ o ho)]
      _ ≤ ∑ s ∈ D.S, D.w s := Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => by
            obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hs
            exact (hOcc o ho).1) fun s _ _ => D.w_nonneg s
      _ ≤ D.M := D.w_sum

/-- The occurrences at scales of mass at most `δ M²`. -/
noncomputable def lightOcc (δ : ℝ) : Finset (ℤ × (Fin 4 → ℤ)) :=
  (D.S.filter fun s => ((D.E s).card : ℝ) ≤ δ * D.M ^ 2).biUnion fun s =>
    (D.E s).image fun x => (s, x)

theorem mem_lightOcc {δ : ℝ} {o : ℤ × (Fin 4 → ℤ)} (ho : o ∈ D.lightOcc δ) :
    o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 ∧ ((D.E o.1).card : ℝ) ≤ δ * D.M ^ 2 := by
  obtain ⟨s, hs, hos⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hos
  obtain ⟨hsS, hsm⟩ := Finset.mem_filter.mp hs
  exact ⟨hsS, hx, hsm⟩

theorem card_lightOcc (δ : ℝ) : ((D.lightOcc δ).card : ℝ) =
    ∑ s ∈ D.S.filter (fun s => ((D.E s).card : ℝ) ≤ δ * D.M ^ 2), ((D.E s).card : ℝ) := by
  unfold lightOcc
  rw [Finset.card_biUnion]
  · push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.card_image_of_injective _ fun x y h => (Prod.mk.inj h).2]
  · intro s _ s' _ hne
    refine Finset.disjoint_left.mpr fun o ho ho' => hne ?_
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp ho'
    exact (Prod.mk.inj hy).1.symm

theorem lightOcc_scale_mass {δ : ℝ} (hδ : 0 ≤ δ) (s : ℤ) :
    (((D.lightOcc δ).filter fun o => o.1 = s).card : ℝ) ≤ δ * D.M ^ 2 := by
  classical
  rcases ((D.lightOcc δ).filter fun o => o.1 = s).eq_empty_or_nonempty with h | ⟨o, ho⟩
  · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
  · obtain ⟨hoL, hos⟩ := Finset.mem_filter.mp ho
    have hm := (D.mem_lightOcc hoL).2.2
    rw [hos] at hm
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card_of_injOn (fun o => o.2) ?_ ?_)) hm
    · intro o' ho'
      obtain ⟨ho'L, ho's⟩ := Finset.mem_filter.mp ho'
      have := (D.mem_lightOcc ho'L).2.1
      rwa [ho's] at this
    · intro o₁ h₁ o₂ h₂ h
      exact Prod.ext ((Finset.mem_filter.mp h₁).2.trans (Finset.mem_filter.mp h₂).2.symm) h

/-- Blueprint lines 2613-2626 (difference covers in every block and role): for occurrences split
into blocks `β` with later blocks at strictly smaller scales, there are block widths `ε_b` with
`ε_b ≤ 17 ν R_b^+`, where `R_b^+` is below every scale of an earlier block, and in each block
and core role a cover family as in `cover_family`. -/
theorem block_covers (Occ : Finset (ℤ × (Fin 4 → ℤ)))
    (hOcc : ∀ o ∈ Occ, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) (β : ℤ → ℕ)
    (hβlt : ∀ o ∈ Occ, ∀ o' ∈ Occ, β o.1 < β o'.1 → o'.1 < o.1) (N₀ : ℕ)
    (hN₀ : 24 * D.B ≤ N₀) {η : ℝ} (hη : 0 < η) :
    ∃ (Rp : ℕ → ℝ) (ε : ℕ → ℕ) (𝓑 : ℕ → Fin 4 → Finset (Finset ℤ))
      (Pc : ℕ → Fin 4 → Finset ℤ → Finset ℤ),
      (∀ b, ∀ o ∈ Occ, β o.1 < b → Rp b < D.R o.1) ∧ (∀ b, (ε b : ℝ) ≤ 17 * D.ν * Rp b) ∧
      (∀ b, ∀ i ∈ D.core, ∀ B ∈ 𝓑 b i, B ⊆ D.A i) ∧
      (∀ b, ∀ i ∈ D.core, ∀ B ∈ 𝓑 b i, ∀ B' ∈ 𝓑 b i, B ≠ B' → Disjoint B B') ∧
      (∀ b, ∀ i ∈ D.core, ((𝓑 b i).card : ℝ) ≤ 3 / η) ∧
      (∀ b, ∀ i ∈ D.core, ∀ B ∈ 𝓑 b i, ((Pc b i B).card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
        ∀ a ∈ B, ∀ a' ∈ B, ∃ p ∈ Pc b i B, a - a' - p ∈ shiftBox D.ζ N₀ (ε b) 2) ∧
      (∀ b, ∀ i ∈ D.core, (((Occ.filter fun o => β o.1 = b).filter
        fun o => ∀ B ∈ 𝓑 b i, o.2 i ∉ B).card : ℝ) ≤ η * D.L * D.M ^ 2) := by
  classical
  have hν : 0 < D.ν := lt_of_lt_of_le D.μ_pos D.μ_le_ν
  set Ob : ℕ → Finset (ℤ × (Fin 4 → ℤ)) := fun b => Occ.filter fun o => β o.1 = b
  set Rp : ℕ → ℝ := fun b => if h : ((Ob b).image Prod.fst).Nonempty then
    D.R (((Ob b).image Prod.fst).max' h) else 0
  have hRp_le : ∀ b, ∀ o ∈ Ob b, D.R o.1 ≤ Rp b := by
    intro b o ho
    have hne : ((Ob b).image Prod.fst).Nonempty := ⟨_, Finset.mem_image_of_mem _ ho⟩
    simp only [Rp, hne, ↓reduceDIte]
    exact D.R_strictMono.monotone (Finset.le_max' _ _ (Finset.mem_image_of_mem _ ho))
  have hRp_lt : ∀ b, ∀ o ∈ Occ, β o.1 < b → Rp b < D.R o.1 := by
    intro b o ho hlt
    by_cases hne : ((Ob b).image Prod.fst).Nonempty
    · simp only [Rp, hne, ↓reduceDIte]
      obtain ⟨o', ho', hos⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
      obtain ⟨ho'O, ho'b⟩ := Finset.mem_filter.mp ho'
      rw [← hos]
      exact D.R_strictMono (hβlt o ho o' ho'O (ho'b ▸ hlt))
    · simp only [Rp, hne, ↓reduceDIte]; exact D.R_pos _
  have hRp1 : ∀ b, Rp b = 0 ∨ 1 ≤ D.ν * Rp b := by
    intro b
    by_cases hne : ((Ob b).image Prod.fst).Nonempty
    · right
      simp only [Rp, hne, ↓reduceDIte]
      obtain ⟨o', ho', hos⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
      have hS := (hOcc o' (Finset.mem_filter.mp ho').1).1
      rw [← hos]
      have h1 := D.one_le_μR o'.1 hS
      have h2 : D.μ * D.R o'.1 ≤ D.ν * D.R o'.1 :=
        mul_le_mul_of_nonneg_right D.μ_le_ν (D.R_pos _).le
      exact h1.trans h2
    · left; simp only [Rp, hne, ↓reduceDIte]
  have hRp0 : ∀ b, 0 ≤ Rp b := by
    intro b
    rcases hRp1 b with h | h
    · rw [h]
    · by_contra hc; push Not at hc; nlinarith
  set ε : ℕ → ℕ := fun b => ⌈16 * D.ν * Rp b⌉₊
  have hε17 : ∀ b, (ε b : ℝ) ≤ 17 * D.ν * Rp b := by
    intro b
    rcases hRp1 b with h | h
    · simp [ε, h]
    · have h0 : (0 : ℝ) ≤ 16 * D.ν * Rp b :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hν.le) (hRp0 b)
      have := Nat.ceil_lt_add_one h0
      linarith
  have hε4 : ∀ b, 4 * D.ν * Rp b ≤ ε b := by
    intro b
    refine le_trans ?_ (Nat.le_ceil _)
    have := mul_nonneg hν.le (hRp0 b)
    linarith
  -- the cover families
  have hcf : ∀ b : ℕ, ∀ i : Fin 4, ∃ 𝓑 : Finset (Finset ℤ), i ∈ D.core →
      (∀ B ∈ 𝓑, B ⊆ D.A i) ∧ (∀ B ∈ 𝓑, ∀ B' ∈ 𝓑, B ≠ B' → Disjoint B B') ∧
      (∀ B ∈ 𝓑, η * D.M / 3 ≤ B.card) ∧
      (∀ B ∈ 𝓑, ∃ P : Finset ℤ, (P.card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
        ∀ a ∈ B, ∀ a' ∈ B, ∃ p ∈ P, a - a' - p ∈ shiftBox D.ζ N₀ (ε b) 2) ∧
      (((Ob b).filter fun o => ∀ B ∈ 𝓑, o.2 i ∉ B).card : ℝ) ≤ η * D.L * D.M ^ 2 := by
    intro b i
    by_cases hi : i ∈ D.core
    · obtain ⟨j, hj, k, hk, hij, hik, hjk⟩ := D.exists_two_other hi
      obtain ⟨l, hl⟩ : ∃ l, l ∉ ({i, j, k} : Finset (Fin 4)) := by
        by_contra h
        push Not at h
        have : (Finset.univ : Finset (Fin 4)) ⊆ {i, j, k} := fun x _ => h x
        have := Finset.card_le_card this
        rw [Finset.card_univ, Fintype.card_fin] at this
        have := Finset.card_le_three (a := i) (b := j) (c := k)
        omega
      obtain ⟨𝓑, h1, h2, h3, h4, h5⟩ := D.cover_family (Ob b)
        (fun o ho => hOcc o (Finset.mem_filter.mp ho).1) hi hj hk hij hik hjk hl
        (hRp_le b) N₀ (ε b) hN₀ (hε4 b) hη
      exact ⟨𝓑, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose 𝓑 h𝓑 using hcf
  have hPc : ∀ b : ℕ, ∀ i : Fin 4, ∀ B : Finset ℤ, ∃ P : Finset ℤ,
      i ∈ D.core → B ∈ 𝓑 b i → (P.card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
        ∀ a ∈ B, ∀ a' ∈ B, ∃ p ∈ P, a - a' - p ∈ shiftBox D.ζ N₀ (ε b) 2 := by
    intro b i B
    by_cases h : i ∈ D.core ∧ B ∈ 𝓑 b i
    · obtain ⟨P, hP⟩ := (h𝓑 b i h.1).2.2.2.1 B h.2
      exact ⟨P, fun _ _ => hP⟩
    · exact ⟨∅, fun hi hB => absurd ⟨hi, hB⟩ h⟩
  choose Pc hPc' using hPc
  refine ⟨Rp, ε, 𝓑, Pc, hRp_lt, hε17, fun b i hi => (h𝓑 b i hi).1,
    fun b i hi => (h𝓑 b i hi).2.1, fun b i hi => D.cover_family_card hi (h𝓑 b i hi).1
      (h𝓑 b i hi).2.1 hη (h𝓑 b i hi).2.2.1, fun b i hi B hB => hPc' b i B hi hB,
    fun b i hi => (h𝓑 b i hi).2.2.2.2⟩

/-- An enumeration of a three-element set of roles. -/
noncomputable def enumRoles (T : Finset (Fin 4)) : Fin 3 → Fin 4 :=
  if h : T.card = 3 then fun j => T.orderEmbOfFin h j else fun _ => 0

theorem enumRoles_spec {T : Finset (Fin 4)} (h : T.card = 3) :
    Function.Injective (enumRoles T) ∧ ∀ j, enumRoles T j ∈ T := by
  unfold enumRoles
  simp only [h, ↓reduceDIte]
  exact ⟨(T.orderEmbOfFin h).injective, fun j => T.orderEmbOfFin_mem h j⟩

/-- Blueprint lines 2634-2638 (combinations): occurrences all of whose core labels are covered
in their own block and which have at least three future roles are grouped by their block, a
triple of future roles and future cover subsets for them; there are at most
`J₀ · 4 · (12 J₀/η)³` combinations, and each has mass at most `Y` by `combination_bound`. -/
theorem combinations_mass_le (Occ : Finset (ℤ × (Fin 4 → ℤ)))
    (hOcc : ∀ o ∈ Occ, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) {δ : ℝ} (hδ : 0 < δ)
    (hδm : ∀ s, ((Occ.filter fun o => o.1 = s).card : ℝ) ≤ δ * D.M ^ 2)
    (hOccL : (Occ.card : ℝ) ≤ D.L * D.M ^ 2) (β : ℤ → ℕ) (J₀ : ℕ)
    (hβ : ∀ o ∈ Occ, β o.1 < J₀) (N₀ : ℕ) (hN₀ : (N₀ : ℝ) ≤ 33 * D.B) {η : ℝ} (hη : 0 < η)
    (Rp : ℕ → ℝ) (ε : ℕ → ℕ) (𝓑 : ℕ → Fin 4 → Finset (Finset ℤ))
    (Pc : ℕ → Fin 4 → Finset ℤ → Finset ℤ)
    (hRp : ∀ b, ∀ o ∈ Occ, β o.1 < b → Rp b < D.R o.1) (hε : ∀ b, (ε b : ℝ) ≤ 17 * D.ν * Rp b)
    (h𝓑card : ∀ b, ∀ i ∈ D.core, ((𝓑 b i).card : ℝ) ≤ 3 / η)
    (hPc : ∀ b, ∀ i ∈ D.core, ∀ B ∈ 𝓑 b i, ((Pc b i B).card : ℝ) ≤ 160000 / η ^ 5 * D.M ∧
      ∀ a ∈ B, ∀ a' ∈ B, ∃ p ∈ Pc b i B, a - a' - p ∈ shiftBox D.ζ N₀ (ε b) 2)
    {g : ℕ} (hg : 1 ≤ g) (hgΓ : 612000000 * ((D.d : ℝ) + 1) ^ 2 * D.ν ≤ 2 ^ g * D.μ)
    (hQ : 7200000 * ((D.d : ℝ) + 1) ^ 2 * D.B ≤ D.Q)
    (hSg : 700000 * ((D.d : ℝ) + 1) ^ 2 * D.ν ≤ D.Sg) {Y : ℝ}
    (hY1 : 12 * g * δ * D.M ^ 2 ≤ Y)
    (hY2 : ∀ x : ℝ, 0 ≤ x → (x / D.M ^ 2) ^ 10 ≤
      10 ^ 6 * δ * g * (160000 / η ^ 5) ^ 7 * D.L ^ 9 → x ≤ Y) :
    ((Occ.filter fun o => 3 ≤ (D.core.filter fun i => ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
      ∃ B ∈ 𝓑 b' i, o.2 i ∈ B).card).card : ℝ) ≤ J₀ * 4 * (12 * J₀ / η) ^ 3 * Y := by
  classical
  have hM0 : 0 < D.M := by linarith [D.one_le_M]
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY1
  set! fut : ℤ × (Fin 4 → ℤ) → Finset (Fin 4) := fun o => D.core.filter fun i =>
    ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧ ∃ B ∈ 𝓑 b' i, o.2 i ∈ B
  set U₃ := Occ.filter fun o => 3 ≤ (fut o).card
  -- choices: a triple of future roles, future blocks and subsets
  have hT : ∀ o, ∃ T : Finset (Fin 4), T ⊆ fut o ∧ (3 ≤ (fut o).card → T.card = 3) := by
    intro o
    by_cases h : 3 ≤ (fut o).card
    · obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq h
      exact ⟨T, hT, fun _ => hTc⟩
    · exact ⟨∅, Finset.empty_subset _, fun h' => absurd h' h⟩
  choose T hTsub hTcard using hT
  have hsel : ∀ o i, ∃ p : ℕ × Finset ℤ, i ∈ fut o →
      p.1 ∈ Finset.range J₀ ∧ β o.1 < p.1 ∧ p.2 ∈ 𝓑 p.1 i ∧ o.2 i ∈ p.2 := by
    intro o i
    by_cases h : i ∈ fut o
    · obtain ⟨-, b', hb', hlt, B, hB, hoB⟩ := Finset.mem_filter.mp h
      exact ⟨(b', B), fun _ => ⟨hb', hlt, hB, hoB⟩⟩
    · exact ⟨(0, ∅), fun h' => absurd h' h⟩
  choose sel hsel using hsel
  set! key : ℤ × (Fin 4 → ℤ) → (ℕ × Finset (Fin 4)) × (Fin 3 → ℕ × Finset ℤ) := fun o =>
    ((β o.1, T o), fun j => sel o (enumRoles (T o) j))
  -- the key space
  set! AllPairs := (Finset.range J₀ ×ˢ D.core).biUnion fun p => (𝓑 p.1 p.2).image fun B => (p.1, B)
  have hAll : (AllPairs.card : ℝ) ≤ 12 * J₀ / η := by
    refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
    push_cast
    calc ∑ p ∈ Finset.range J₀ ×ˢ D.core, (((𝓑 p.1 p.2).image fun B => (p.1, B)).card : ℝ)
        ≤ ∑ _p ∈ Finset.range J₀ ×ˢ D.core, 3 / η := by
          refine Finset.sum_le_sum fun p hp => ?_
          exact (Nat.cast_le.mpr Finset.card_image_le).trans
            (h𝓑card p.1 p.2 (Finset.mem_product.mp hp).2)
      _ = J₀ * D.core.card * (3 / η) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]; push_cast
          ring
      _ ≤ J₀ * 4 * (3 / η) := by
          gcongr
          exact_mod_cast (Finset.card_le_univ D.core).trans (by simp)
      _ = 12 * J₀ / η := by ring
  set! KS := (Finset.range J₀ ×ˢ D.core.powersetCard 3) ×ˢ
    Fintype.piFinset fun _ : Fin 3 => AllPairs
  have hKS : (KS.card : ℝ) ≤ J₀ * 4 * (12 * J₀ / η) ^ 3 := by
    simp only [KS, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.card_range]
    push_cast
    have h4 : ((D.core.powersetCard 3).card : ℝ) ≤ 4 := by
      rw [Finset.card_powersetCard]
      have : D.core.card ≤ 4 := (Finset.card_le_univ D.core).trans (by simp)
      have h' : D.core.card.choose 3 ≤ 4 := by
        interval_cases D.core.card <;> decide
      exact_mod_cast h'
    have h0 : (0 : ℝ) ≤ (AllPairs.card : ℝ) ^ 3 := by positivity
    calc (J₀ : ℝ) * (D.core.powersetCard 3).card * (AllPairs.card : ℝ) ^ 3
        ≤ J₀ * 4 * (AllPairs.card : ℝ) ^ 3 := by gcongr
      _ ≤ J₀ * 4 * (12 * J₀ / η) ^ 3 := by gcongr
  have hfutC : ∀ o, fut o ⊆ D.core := fun o => Finset.filter_subset _ _
  have hkeyKS : ∀ o ∈ U₃, key o ∈ KS := by
    intro o ho
    obtain ⟨hoO, ho3⟩ := Finset.mem_filter.mp ho
    have hT3 := hTcard o ho3
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hβ o hoO),
      Finset.mem_powersetCard.mpr ⟨(hTsub o).trans (hfutC o), hT3⟩⟩,
      Fintype.mem_piFinset.mpr fun j => ?_⟩
    have hi : enumRoles (T o) j ∈ fut o := hTsub o ((enumRoles_spec hT3).2 j)
    obtain ⟨hb, -, hB, -⟩ := hsel o _ hi
    exact Finset.mem_biUnion.mpr ⟨((sel o (enumRoles (T o) j)).1, enumRoles (T o) j),
      Finset.mem_product.mpr ⟨hb, hfutC o hi⟩, Finset.mem_image.mpr ⟨_, hB, rfl⟩⟩
  have hclass : ∀ κ, ((U₃.filter fun o => key o = κ).card : ℝ) ≤ Y := by
    intro κ
    set C := U₃.filter fun o => key o = κ
    rcases C.eq_empty_or_nonempty with hC | ⟨o₀, ho₀⟩
    · rw [hC, Finset.card_empty, Nat.cast_zero]; exact hY0
    have hCU : ∀ o ∈ C, o ∈ U₃ := fun o ho => (Finset.mem_filter.mp ho).1
    have hCO : ∀ o ∈ C, o ∈ Occ := fun o ho => (Finset.mem_filter.mp (hCU o ho)).1
    have hkey : ∀ o ∈ C, key o = key o₀ := fun o ho =>
      (Finset.mem_filter.mp ho).2.trans (Finset.mem_filter.mp ho₀).2.symm
    have hT₀3 : (T o₀).card = 3 := hTcard o₀ (Finset.mem_filter.mp (hCU o₀ ho₀)).2
    obtain ⟨he, heT⟩ := enumRoles_spec hT₀3
    set e := enumRoles (T o₀)
    have hTo : ∀ o ∈ C, T o = T o₀ := fun o ho => congrArg (fun k => k.1.2) (hkey o ho)
    have hselo : ∀ o ∈ C, ∀ j, sel o (e j) = sel o₀ (e j) := by
      intro o ho j
      have := congrFun (congrArg Prod.snd (hkey o ho)) j
      simp only [key] at this
      rwa [hTo o ho] at this
    have hfut : ∀ o ∈ C, ∀ j, e j ∈ fut o := by
      intro o ho j
      have h1 : e j ∈ T o := by rw [hTo o ho]; exact heT j
      exact hTsub o h1
    have heC : ∀ j, e j ∈ D.core := fun j => hfutC o₀ (hfut o₀ ho₀ j)
    obtain ⟨l, hl⟩ : ∃ l, l ∉ T o₀ := by
      by_contra h
      push Not at h
      have : (Finset.univ : Finset (Fin 4)) ⊆ T o₀ := fun x _ => h x
      have := Finset.card_le_card this
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hel : ∀ j, e j ≠ l := fun j h => hl (h ▸ heT j)
    set! p : Fin 3 → ℕ × Finset ℤ := fun j => sel o₀ (e j)
    have hp : ∀ j, (p j).2 ∈ 𝓑 (p j).1 (e j) := fun j => (hsel o₀ (e j) (hfut o₀ ho₀ j)).2.2.1
    have hCbound := D.combination_bound C (fun o ho => hOcc o (hCO o ho)) hδ
      (fun s => le_trans (Nat.cast_le.mpr (Finset.card_le_card
        (Finset.filter_subset_filter _ fun o ho => hCO o ho))) (hδm s))
      e he heC hel (fun j => (p j).2) (fun j => Pc (p j).1 (e j) (p j).2) (fun j => ε (p j).1) N₀
      (fun j => Rp (p j).1)
      (fun o ho j => by
        have := (hsel o (e j) (hfut o ho j)).2.2.2
        rwa [hselo o ho j] at this)
      (fun j => (hPc (p j).1 (e j) (heC j) (p j).2 (hp j)).2) (K₁ := 160000 / η ^ 5)
      (by positivity) (fun j => (hPc (p j).1 (e j) (heC j) (p j).2 (hp j)).1)
      (fun j => hε (p j).1)
      (fun j o ho => by
        have := (hsel o (e j) (hfut o ho j)).2.1
        rw [hselo o ho j] at this
        exact hRp _ o (hCO o ho) this)
      hN₀ hg hgΓ hQ hSg
    by_cases hbig : 12 * g * δ * D.M ^ 2 < C.card
    · exact hY2 _ (Nat.cast_nonneg _) (hCbound hbig (le_trans (Nat.cast_le.mpr
        (Finset.card_le_card fun o ho => hCO o ho)) hOccL))
    · push Not at hbig
      exact hbig.trans hY1
  have hU : (U₃.card : ℝ) ≤ KS.card * Y := by
    rw [Finset.card_eq_sum_card_fiberwise hkeyKS]
    push_cast
    calc ∑ κ ∈ KS, ((U₃.filter fun o => key o = κ).card : ℝ) ≤ ∑ _κ ∈ KS, Y :=
          Finset.sum_le_sum fun κ _ => hclass κ
      _ = KS.card * Y := by rw [Finset.sum_const, nsmul_eq_mul]
  exact hU.trans (mul_le_mul_of_nonneg_right hKS hY0)

/-- Blueprint lines 2628-2633 (all nonfuture terms): occurrences with every core label covered
in its block but fewer than three future core roles have mass at most `16 √(c L) M`. -/
theorem nonfuture_mass_le (Occ : Finset (ℤ × (Fin 4 → ℤ)))
    (hOcc : ∀ o ∈ Occ, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1) (β : ℤ → ℕ) (J₀ : ℕ)
    (hβ : ∀ o ∈ Occ, β o.1 < J₀) (𝓑 : ℕ → Fin 4 → Finset (Finset ℤ))
    (hA : ∀ b, ∀ i ∈ D.core, ∀ B ∈ 𝓑 b i, B ⊆ D.A i) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ b, ((Occ.filter fun o => β o.1 = b).card : ℝ) ≤ c) :
    ((Occ.filter fun o : ℤ × (Fin 4 → ℤ) => (∀ i ∈ D.core, ∃ B ∈ 𝓑 (β o.1) i, o.2 i ∈ B) ∧
      (D.core.filter fun i => ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
        ∃ B ∈ 𝓑 b' i, o.2 i ∈ B).card < 3).card : ℝ) ≤
      16 * (Real.sqrt (c * D.L) * D.M) := by
  classical
  have hL : (1 : ℝ) ≤ D.L := by exact_mod_cast D.one_le_L
  have hM0 : 0 ≤ D.M := by linarith [D.one_le_M]
  set Cov : ℕ → Fin 4 → Finset ℤ := fun b i => (𝓑 b i).biUnion id
  set NF : ℕ → Fin 4 → Finset ℤ := fun b i =>
    Cov b i \ ((Finset.range J₀).filter (fun b' => b < b')).biUnion fun b' => Cov b' i
  have hNFA : ∀ b, ∀ r ∈ D.core, NF b r ⊆ D.A r := by
    intro b r hr x hx
    obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hx).1
    exact hA b r hr B hB hxB
  have hNFdis : ∀ r ∈ D.core, ∀ b ∈ Finset.range J₀, ∀ b' ∈ Finset.range J₀, b ≠ b' →
      Disjoint (NF b r) (NF b' r) := by
    intro r _ b hb b' hb' hne
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    rcases lt_or_gt_of_ne hne with h | h
    · exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
        ⟨b', Finset.mem_filter.mpr ⟨hb', h⟩, (Finset.mem_sdiff.mp hx').1⟩)
    · exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, h⟩, (Finset.mem_sdiff.mp hx).1⟩)
  set U₂ := Occ.filter fun o : ℤ × (Fin 4 → ℤ) => (∀ i ∈ D.core, ∃ B ∈ 𝓑 (β o.1) i, o.2 i ∈ B) ∧
      (D.core.filter fun i => ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
        ∃ B ∈ 𝓑 b' i, o.2 i ∈ B).card < 3
  -- nonfuture roles have nonfuture labels
  have hnf : ∀ o ∈ U₂, ∀ i ∈ D.core, ¬ (∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
      ∃ B ∈ 𝓑 b' i, o.2 i ∈ B) → o.2 i ∈ NF (β o.1) i := by
    intro o ho i hi hfut
    obtain ⟨-, hcov, -⟩ := Finset.mem_filter.mp ho
    obtain ⟨B, hB, hoB⟩ := hcov i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨B, hB, hoB⟩, fun h => hfut ?_⟩
    obtain ⟨b', hb', hB'⟩ := Finset.mem_biUnion.mp h
    obtain ⟨B', hB'', hoB'⟩ := Finset.mem_biUnion.mp hB'
    obtain ⟨hb'r, hlt⟩ := Finset.mem_filter.mp hb'
    exact ⟨b', hb'r, hlt, B', hB'', hoB'⟩
  have hpair : ∀ i ∈ D.core, ∀ j ∈ D.core, i ≠ j →
      ((Occ.filter fun o => o.2 i ∈ NF (β o.1) i ∧ o.2 j ∈ NF (β o.1) j).card : ℝ) ≤
        Real.sqrt (c * D.L) * D.M := fun i hi j hj hij =>
    D.pair_nonfuture_mass_le Occ hOcc β J₀ hβ NF hi hj hij hNFA hNFdis hc hblock
  rcases D.core_card with h3 | h4
  · -- three core roles: one nonfuture core role and the side role
    have hside : ∀ i ∈ D.core,
        ((Occ.filter fun o => o.2 i ∈ NF (β o.1) i).card : ℝ) ≤ Real.sqrt (c * D.L) * D.M := by
      intro i hi
      refine (D.side_nonfuture_mass_le h3 Occ hOcc β J₀ hβ NF hi (fun b => hNFA b i hi)
        (hNFdis i hi) hc hblock).trans ?_
      gcongr
    have hsub : U₂ ⊆ D.core.biUnion fun i => Occ.filter fun o => o.2 i ∈ NF (β o.1) i := by
      intro o ho
      have hlt := (Finset.mem_filter.mp ho).2.2
      obtain ⟨i, hi, hnot⟩ : ∃ i ∈ D.core, ¬ (∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
          ∃ B ∈ 𝓑 b' i, o.2 i ∈ B) := by
        by_contra h
        push Not at h
        rw [Finset.filter_true_of_mem h, h3] at hlt
        exact lt_irrefl _ hlt
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ho).1,
        hnf o ho i hi hnot⟩⟩
    refine (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans ?_
    push_cast
    calc ∑ i ∈ D.core, ((Occ.filter fun o => o.2 i ∈ NF (β o.1) i).card : ℝ)
        ≤ ∑ _i ∈ D.core, Real.sqrt (c * D.L) * D.M := Finset.sum_le_sum hside
      _ = 3 * (Real.sqrt (c * D.L) * D.M) := by rw [Finset.sum_const, h3]; simp
      _ ≤ 16 * (Real.sqrt (c * D.L) * D.M) := by
          have : 0 ≤ Real.sqrt (c * D.L) * D.M :=
            mul_nonneg (Real.sqrt_nonneg _) (by linarith [D.one_le_M])
          linarith
  · -- four core roles: two nonfuture core roles
    have hsub : U₂ ⊆ ((D.core ×ˢ D.core).filter fun p => p.1 ≠ p.2).biUnion fun p =>
        Occ.filter fun o => o.2 p.1 ∈ NF (β o.1) p.1 ∧ o.2 p.2 ∈ NF (β o.1) p.2 := by
      intro o ho
      have hlt := (Finset.mem_filter.mp ho).2.2
      set F := D.core.filter fun i => ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
        ∃ B ∈ 𝓑 b' i, o.2 i ∈ B
      have hltF : F.card < 3 := hlt
      have e : (D.core \ F).card = D.core.card - F.card :=
        Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
      have hcard : 2 ≤ (D.core \ F).card := by
        rw [e, h4]; omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
      obtain ⟨hic, hiF⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨hjc, hjF⟩ := Finset.mem_sdiff.mp hj
      have hi' : ¬ (∃ b' ∈ Finset.range J₀, β o.1 < b' ∧ ∃ B ∈ 𝓑 b' i, o.2 i ∈ B) :=
        fun h => hiF (Finset.mem_filter.mpr ⟨hic, h⟩)
      have hj' : ¬ (∃ b' ∈ Finset.range J₀, β o.1 < b' ∧ ∃ B ∈ 𝓑 b' j, o.2 j ∈ B) :=
        fun h => hjF (Finset.mem_filter.mpr ⟨hjc, h⟩)
      exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hic, hjc⟩, hij⟩, Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp ho).1, hnf o ho i hic hi', hnf o ho j hjc hj'⟩⟩
    refine (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans ?_
    push_cast
    have hpc : (((D.core ×ˢ D.core).filter fun p => p.1 ≠ p.2).card : ℝ) ≤ 16 := by
      have := Finset.card_le_card (Finset.filter_subset (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2)
        (D.core ×ˢ D.core))
      rw [Finset.card_product, h4] at this
      exact_mod_cast this
    have h0 : 0 ≤ Real.sqrt (c * D.L) * D.M :=
      mul_nonneg (Real.sqrt_nonneg _) (by linarith [D.one_le_M])
    calc ∑ p ∈ (D.core ×ˢ D.core).filter (fun p => p.1 ≠ p.2),
          ((Occ.filter fun o => o.2 p.1 ∈ NF (β o.1) p.1 ∧ o.2 p.2 ∈ NF (β o.1) p.2).card : ℝ)
        ≤ ∑ _p ∈ (D.core ×ˢ D.core).filter (fun p => p.1 ≠ p.2),
            Real.sqrt (c * D.L) * D.M := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hpc', hne⟩ := Finset.mem_filter.mp hp
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpc'
          exact hpair p.1 h1 p.2 h2 hne
      _ = _ * (Real.sqrt (c * D.L) * D.M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 16 * (Real.sqrt (c * D.L) * D.M) := by gcongr

end SparseCountData

/-- Blueprint lines 2700-2705 (final count): the uncovered, nonfuture and combination masses sum
to at most `10¹¹ ℓ L¹² τ M²` (via `eq:count-balance`). -/
theorem sparse_final_arith {X J₀ L ℓ τ M U₁ U₂ U₃ : ℝ} (hτ0 : 0 < τ)
    (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) (hM : 0 < M) (hJ0 : 0 ≤ J₀) (hJ : J₀ ≤ 3 * L * τ⁻¹ ^ 2)
    (hX : X ≤ U₁ + U₂ + U₃) (h1 : U₁ ≤ J₀ * 4 * (τ ^ 3 / L * L * M ^ 2))
    (h2 : U₂ ≤ 16 * (Real.sqrt (2 * (τ ^ 2 * M ^ 2) * L) * M))
    (h3 : U₃ ≤ J₀ * 4 * (12 * J₀ / (τ ^ 3 / L)) ^ 3 *
      (10 ^ 5 * ℓ * (τ ^ 3 / L)⁻¹ ^ 4 * L * τ ^ 30 * M ^ 2)) :
    X ≤ 10 ^ 11 * ℓ * L ^ 12 * τ * M ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hM2 : 0 < M ^ 2 := by positivity
  have e1 : J₀ * 4 * (τ ^ 3 / L * L * M ^ 2) = 4 * (J₀ * τ ^ 3) * M ^ 2 := by
    field_simp
  have e2 : Real.sqrt (2 * (τ ^ 2 * M ^ 2) * L) * M =
      Real.sqrt 2 * (Real.sqrt L * τ) * M ^ 2 := by
    rw [show 2 * (τ ^ 2 * M ^ 2) * L = 2 * L * (τ * M) ^ 2 by ring,
      Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num)]
    ring
  have e3 : J₀ * 4 * (12 * J₀ / (τ ^ 3 / L)) ^ 3 *
      (10 ^ 5 * ℓ * (τ ^ 3 / L)⁻¹ ^ 4 * L * τ ^ 30 * M ^ 2) =
      691200000 * (ℓ * L * J₀ ^ 4 * (τ ^ 3 / L)⁻¹ ^ 7 * τ ^ 30) * M ^ 2 := by
    field_simp
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hbal := count_balance_bound hL hℓ hτ0 hJ0 hJ
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hA : 0 ≤ J₀ * τ ^ 3 := by positivity
  have hB : 0 ≤ Real.sqrt L * τ := by positivity
  have hC : 0 ≤ ℓ * L * J₀ ^ 4 * (τ ^ 3 / L)⁻¹ ^ 7 * τ ^ 30 := by positivity
  have hsum : J₀ * τ ^ 3 + Real.sqrt L * τ + ℓ * L * J₀ ^ 4 * (τ ^ 3 / L)⁻¹ ^ 7 * τ ^ 30 ≤
      85 * ℓ * L ^ 12 * τ := hbal
  have h2' : U₂ ≤ 32 * (Real.sqrt L * τ) * M ^ 2 := by
    refine h2.trans ?_
    have : Real.sqrt 2 * (Real.sqrt L * τ) * M ^ 2 ≤ 2 * (Real.sqrt L * τ) * M ^ 2 := by
      gcongr
    linarith
  calc X ≤ U₁ + U₂ + U₃ := hX
    _ ≤ 691200000 * (J₀ * τ ^ 3 + Real.sqrt L * τ +
          ℓ * L * J₀ ^ 4 * (τ ^ 3 / L)⁻¹ ^ 7 * τ ^ 30) * M ^ 2 := by
        nlinarith only [mul_nonneg hA hM2.le, mul_nonneg hB hM2.le, mul_nonneg hC hM2.le, h1, h3,
            h2']
    _ ≤ 691200000 * (85 * ℓ * L ^ 12 * τ) * M ^ 2 := by gcongr
    _ ≤ 10 ^ 11 * ℓ * L ^ 12 * τ * M ^ 2 := by
        have : 0 ≤ ℓ * L ^ 12 * τ * M ^ 2 := by positivity
        nlinarith only [hbal, hA, hB, hC]

/-- The logarithmic scale margin: there is `g ≤ 32 ℓ` with `2^g μ ≥ 612000000 (d+1)² ν`, where
`ℓ = 1 + log₂(2 + (d+1)² ν/μ)`. -/
theorem exists_scale_margin {d : ℕ} {μ ν : ℝ} (hμ : 0 < μ) (hμν : μ ≤ ν) :
    ∃ g : ℕ, 1 ≤ g ∧ 612000000 * ((d : ℝ) + 1) ^ 2 * ν ≤ 2 ^ g * μ ∧
      (g : ℝ) ≤ 32 * (1 + Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * ν / μ)) := by
  have hν : 0 < ν := lt_of_lt_of_le hμ hμν
  set y := ((d : ℝ) + 1) ^ 2 * ν / μ
  have hy : 0 < y := by positivity
  set X := 612000000 * y
  have hX : 0 < X := by positivity
  refine ⟨⌈Real.logb 2 X⌉₊ + 1, by omega, ?_, ?_⟩
  · have h1 : X ≤ (2 : ℝ) ^ (⌈Real.logb 2 X⌉₊ + 1) := by
      rw [← Real.rpow_natCast]
      calc X = (2 : ℝ) ^ (Real.logb 2 X) := (Real.rpow_logb (by norm_num) (by norm_num) hX).symm
        _ ≤ (2 : ℝ) ^ (((⌈Real.logb 2 X⌉₊ + 1 : ℕ) : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            push_cast
            linarith [Nat.le_ceil (Real.logb 2 X)]
    have e : 612000000 * ((d : ℝ) + 1) ^ 2 * ν = X * μ := by
      simp only [X, y]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 hμ.le
  · have h1 : Real.logb 2 X = Real.logb 2 612000000 + Real.logb 2 y :=
      Real.logb_mul (by norm_num) hy.ne'
    have h2 : Real.logb 2 612000000 ≤ 30 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
      norm_num
    have h3 : Real.logb 2 y ≤ Real.logb 2 (2 + y) :=
      Real.logb_le_logb_of_le (by norm_num) hy (by linarith)
    have h4 : 1 ≤ Real.logb 2 (2 + y) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
      norm_num; linarith
    have hy1 : 1 ≤ y := by
      rw [le_div_iff₀ hμ, one_mul]
      have : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      nlinarith
    have hX0 : 0 ≤ Real.logb 2 X :=
      Real.logb_nonneg (by norm_num) (by simp only [X]; nlinarith)
    have h5 := Nat.ceil_lt_add_one hX0
    push_cast
    linarith

theorem sparse_Y1_arith {M δ τ g ℓ η L : ℝ} (hM : 0 < M) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : δ = τ ^ 300) (hg : g ≤ 32 * ℓ) (hℓ : 1 ≤ ℓ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hL : 1 ≤ L) : 12 * g * δ * M ^ 2 ≤ 10 ^ 5 * ℓ * η⁻¹ ^ 4 * L * τ ^ 30 * M ^ 2 := by
  have hτ : τ ^ 300 ≤ τ ^ 30 := pow_le_pow_of_le_one hτ0.le hτ1 (by norm_num)
  have hηi : 1 ≤ η⁻¹ ^ 4 := one_le_pow₀ (one_le_inv_iff₀.mpr ⟨hη, hη1⟩)
  have hτ30 : 0 ≤ τ ^ 30 := by positivity
  have hM2 : 0 < M ^ 2 := by positivity
  rw [hδ]
  have h1 : 12 * g * τ ^ 300 ≤ 384 * ℓ * τ ^ 30 := by
    have := mul_le_mul hg hτ (by positivity) (by linarith)
    nlinarith only [this]
  have h2 : 384 * ℓ * τ ^ 30 ≤ 10 ^ 5 * ℓ * η⁻¹ ^ 4 * L * τ ^ 30 := by
    have hlL : 1 ≤ η⁻¹ ^ 4 * L := by nlinarith
    have : 0 ≤ ℓ * τ ^ 30 := by positivity
    nlinarith only [hlL, this]
  have := mul_le_mul_of_nonneg_right (h1.trans h2) hM2.le
  linarith

theorem sparse_Y2_arith {x M δ τ g ℓ η L : ℝ} (hM : 0 < M) (hx : 0 ≤ x) (hτ0 : 0 < τ)
    (hδ : δ = τ ^ 300) (hg : g ≤ 32 * ℓ) (hℓ : 1 ≤ ℓ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hL : 1 ≤ L)
    (h : (x / M ^ 2) ^ 10 ≤ 10 ^ 6 * δ * g * (160000 / η ^ 5) ^ 7 * L ^ 9) :
    x ≤ 10 ^ 5 * ℓ * η⁻¹ ^ 4 * L * τ ^ 30 * M ^ 2 := by
  have hM2 : 0 < M ^ 2 := by positivity
  have hηi : 1 ≤ η⁻¹ := one_le_inv_iff₀.mpr ⟨hη, hη1⟩
  have hY0 : 0 ≤ 10 ^ 5 * ℓ * η⁻¹ ^ 4 * L * τ ^ 30 := by positivity
  suffices hs : x / M ^ 2 ≤ 10 ^ 5 * ℓ * η⁻¹ ^ 4 * L * τ ^ 30 by
    rwa [div_le_iff₀ hM2] at hs
  refine (pow_le_pow_iff_left₀ (div_nonneg hx hM2.le) hY0 (by norm_num : (10 : ℕ) ≠ 0)).mp ?_
  refine h.trans ?_
  have e1 : (160000 / η ^ 5) ^ 7 = 160000 ^ 7 * η⁻¹ ^ 35 := by
    rw [div_pow, ← pow_mul, div_eq_mul_inv, ← inv_pow]
  have e2 : (10 ^ 5 * ℓ * η⁻¹ ^ 4 * L * τ ^ 30) ^ 10 =
      10 ^ 50 * ℓ ^ 10 * η⁻¹ ^ 40 * L ^ 10 * τ ^ 300 := by ring
  rw [e1, e2, hδ]
  have hℓ10 : ℓ ≤ ℓ ^ 10 := le_self_pow₀ hℓ (by norm_num)
  have hη40 : η⁻¹ ^ 35 ≤ η⁻¹ ^ 40 := pow_le_pow_right₀ hηi (by norm_num)
  have hL10 : L ^ 9 ≤ L ^ 10 := pow_le_pow_right₀ hL (by norm_num)
  have hτ300 : 0 ≤ τ ^ 300 := by positivity
  have hgℓ : g ≤ 32 * ℓ ^ 10 := hg.trans (by linarith)
  calc 10 ^ 6 * τ ^ 300 * g * (160000 ^ 7 * η⁻¹ ^ 35) * L ^ 9
      ≤ 10 ^ 6 * τ ^ 300 * (32 * ℓ ^ 10) * (160000 ^ 7 * η⁻¹ ^ 40) * L ^ 10 := by
        gcongr
    _ = (10 ^ 6 * 32 * 160000 ^ 7) * (ℓ ^ 10 * η⁻¹ ^ 40 * L ^ 10 * τ ^ 300) := by ring
    _ ≤ 10 ^ 50 * (ℓ ^ 10 * η⁻¹ ^ 40 * L ^ 10 * τ ^ 300) := by
        gcongr
        norm_num
    _ = 10 ^ 50 * ℓ ^ 10 * η⁻¹ ^ 40 * L ^ 10 * τ ^ 300 := by ring

namespace SparseCountData
variable (D : SparseCountData)

/-- Blueprint `lem:sparse-count`, `eq:sparse-count` for the grid data: with the reserves
`Q ≥ 7.2·10⁶ (d+1)² B` and `Σ ≥ 7·10⁵ (d+1)² ν`, for `0 < δ ≤ 1`,
`Σ_{s : N_s ≤ δ M²} N_s ≤ 10¹¹ ℓ L¹² δ^{1/300} M²` with `ℓ = 1 + log₂(2 + (d+1)² ν/μ)`. -/
theorem sparse_mass_bound (hQ : 7200000 * ((D.d : ℝ) + 1) ^ 2 * D.B ≤ D.Q)
    (hSg : 700000 * ((D.d : ℝ) + 1) ^ 2 * D.ν ≤ D.Sg) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑ s ∈ D.S.filter (fun s => ((D.E s).card : ℝ) ≤ δ * D.M ^ 2), ((D.E s).card : ℝ) ≤
      10 ^ 11 * (1 + Real.logb 2 (2 + ((D.d : ℝ) + 1) ^ 2 * D.ν / D.μ)) * D.L ^ 12 *
        δ ^ (1 / 300 : ℝ) * D.M ^ 2 := by
  classical
  have hM := D.one_le_M
  have hM0 : 0 < D.M := by linarith
  have hL : (1 : ℝ) ≤ D.L := by exact_mod_cast D.one_le_L
  have hL0 : (0 : ℝ) < D.L := by linarith
  set ℓ := 1 + Real.logb 2 (2 + ((D.d : ℝ) + 1) ^ 2 * D.ν / D.μ)
  obtain ⟨g, hg, hgΓ, hgℓ⟩ := exists_scale_margin (d := D.d) D.μ_pos D.μ_le_ν
  have hℓ : 1 ≤ ℓ := by
    have : 0 ≤ Real.logb 2 (2 + ((D.d : ℝ) + 1) ^ 2 * D.ν / D.μ) := by
      refine Real.logb_nonneg (by norm_num) ?_
      have : 0 ≤ ((D.d : ℝ) + 1) ^ 2 * D.ν / D.μ := by
        have := D.μ_pos; have : 0 < D.ν := lt_of_lt_of_le D.μ_pos D.μ_le_ν
        positivity
      linarith
    linarith
  -- the parameters
  set τ := δ ^ (1 / 300 : ℝ)
  have hτ0 : 0 < τ := Real.rpow_pos_of_pos hδ0 _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one hδ0.le hδ1 (by norm_num)
  have hδτ : δ = τ ^ 300 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]; norm_num
  set η := τ ^ 3 / D.L
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [div_le_one hL0]
    exact (pow_le_one₀ hτ0.le hτ1).trans hL
  set θ := τ ^ 2 * D.M ^ 2
  have hθ : 0 < θ := by positivity
  have hδθ : δ * D.M ^ 2 ≤ θ := by
    have : δ ≤ τ ^ 2 := by
      rw [hδτ]; exact pow_le_pow_of_le_one hτ0.le hτ1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  set Occ := D.lightOcc δ
  have hOcc : ∀ o ∈ Occ, o.1 ∈ D.S ∧ o.2 ∈ D.E o.1 := fun o ho =>
    ⟨(D.mem_lightOcc ho).1, (D.mem_lightOcc ho).2.1⟩
  have hOccL : (Occ.card : ℝ) ≤ D.L * D.M ^ 2 := by
    rw [D.card_lightOcc]; exact D.total_mass_le _ (Finset.filter_subset _ _)
  rw [← D.card_lightOcc]
  -- blocks
  set! β := blockIndex Occ θ
  set! J₀ := ⌊(Occ.card : ℝ) / θ⌋₊ + 1
  have hβ : ∀ o ∈ Occ, β o.1 < J₀ := fun o _ => blockIndex_lt Occ hθ o.1
  have hβlt : ∀ o ∈ Occ, ∀ o' ∈ Occ, β o.1 < β o'.1 → o'.1 < o.1 :=
    fun o _ o' _ h => lt_of_blockIndex_lt Occ hθ h
  have hblock : ∀ b, ((Occ.filter fun o => β o.1 = b).card : ℝ) ≤ 2 * θ := fun b =>
    (block_mass_le Occ hθ (D.lightOcc_scale_mass hδ0.le) b).trans (by linarith)
  have hJ0 : (J₀ : ℝ) ≤ 3 * D.L * τ⁻¹ ^ 2 := by
    have h1 : (J₀ : ℝ) ≤ (Occ.card : ℝ) / θ + 1 := by
      simp only [J₀]; push_cast
      linarith [Nat.floor_le (div_nonneg (Nat.cast_nonneg Occ.card) hθ.le)]
    have h2 : (Occ.card : ℝ) / θ ≤ D.L * τ⁻¹ ^ 2 := by
      rw [div_le_iff₀ hθ]
      calc (Occ.card : ℝ) ≤ D.L * D.M ^ 2 := hOccL
        _ = D.L * τ⁻¹ ^ 2 * θ := by simp only [θ]; field_simp
    have h3 : 1 ≤ D.L * τ⁻¹ ^ 2 := by
      have : 1 ≤ τ⁻¹ ^ 2 := one_le_pow₀ (one_le_inv_iff₀.mpr ⟨hτ0, hτ1⟩)
      nlinarith only [hL, this]
    linarith
  -- difference covers in every block and role
  set! N₀ := ⌈32 * D.B⌉₊
  have hN₀ : 24 * D.B ≤ N₀ := le_trans (by linarith [D.one_le_B]) (Nat.le_ceil _)
  have hN₀' : (N₀ : ℝ) ≤ 33 * D.B := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 32 * D.B by linarith [D.one_le_B])
    linarith [D.one_le_B]
  obtain ⟨Rp, ε, 𝓑, Pc, hRp, hε, hA, -, hcard, hPc, hunc⟩ :=
    D.block_covers Occ hOcc β hβlt N₀ hN₀ hη
  -- the three parts
  set! U₁ := Occ.filter fun o : ℤ × (Fin 4 → ℤ) => ∃ i ∈ D.core, ∀ B ∈ 𝓑 (β o.1) i, o.2 i ∉ B
  set! U₂ := Occ.filter fun o : ℤ × (Fin 4 → ℤ) => (∀ i ∈ D.core, ∃ B ∈ 𝓑 (β o.1) i, o.2 i ∈ B) ∧
      (D.core.filter fun i => ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
        ∃ B ∈ 𝓑 b' i, o.2 i ∈ B).card < 3
  set! U₃ := Occ.filter fun o => 3 ≤ (D.core.filter fun i => ∃ b' ∈ Finset.range J₀,
      β o.1 < b' ∧ ∃ B ∈ 𝓑 b' i, o.2 i ∈ B).card
  have hsplit : Occ ⊆ U₁ ∪ U₂ ∪ U₃ := by
    intro o ho
    by_cases h1 : ∃ i ∈ D.core, ∀ B ∈ 𝓑 (β o.1) i, o.2 i ∉ B
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ho, h1⟩))
    · push Not at h1
      by_cases h3 : 3 ≤ (D.core.filter fun i => ∃ b' ∈ Finset.range J₀, β o.1 < b' ∧
          ∃ B ∈ 𝓑 b' i, o.2 i ∈ B).card
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ho, h3⟩)
      · push Not at h3
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨ho, h1, h3⟩))
  have hX : (Occ.card : ℝ) ≤ U₁.card + U₂.card + U₃.card := by
    have := (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast this
  have h1 : (U₁.card : ℝ) ≤ J₀ * 4 * (τ ^ 3 / D.L * D.L * D.M ^ 2) := by
    refine (D.uncovered_mass_le Occ β J₀ hβ 𝓑 fun b _ i hi => hunc b i hi).trans ?_
    have hc4 : (D.core.card : ℝ) ≤ 4 := by
      exact_mod_cast (Finset.card_le_univ D.core).trans (by simp)
    have : 0 ≤ η * D.L * D.M ^ 2 := by positivity
    calc (J₀ : ℝ) * D.core.card * (η * D.L * D.M ^ 2) ≤ J₀ * 4 * (η * D.L * D.M ^ 2) := by
          gcongr
      _ = J₀ * 4 * (τ ^ 3 / D.L * D.L * D.M ^ 2) := rfl
  have h2 : (U₂.card : ℝ) ≤ 16 * (Real.sqrt (2 * θ * D.L) * D.M) :=
    D.nonfuture_mass_le Occ hOcc β J₀ hβ 𝓑 hA (by positivity) hblock
  have h3 : (U₃.card : ℝ) ≤ J₀ * 4 * (12 * J₀ / η) ^ 3 *
      (10 ^ 5 * ℓ * η⁻¹ ^ 4 * D.L * τ ^ 30 * D.M ^ 2) := by
    refine D.combinations_mass_le Occ hOcc hδ0 (D.lightOcc_scale_mass hδ0.le) hOccL β J₀ hβ N₀
      hN₀' hη Rp ε 𝓑 Pc hRp hε hcard hPc hg hgΓ hQ hSg ?_ ?_
    · exact sparse_Y1_arith hM0 hτ0 hτ1 hδτ hgℓ hℓ hη hη1 hL
    · intro x hx hxb
      exact sparse_Y2_arith hM0 hx hτ0 hδτ hgℓ hℓ hη hη1 hL hxb
  exact sparse_final_arith hτ0 hL hℓ hM0 (Nat.cast_nonneg _) hJ0 hX h1 h2 h3 |>.trans_eq rfl

end SparseCountData

/-! ### Reduction to a common grid (lem:sparse-count, blueprint lines 2606-2607) -/

/-- Rounding of a label to the grid `6hℤ`, in grid units. -/
noncomputable def gridLabel (h x : ℝ) : ℤ := 6 * round (x / (6 * h))

theorem gridLabel_err {h : ℝ} (hh : 0 < h) (x : ℝ) : |h * gridLabel h x - x| ≤ 3 * h := by
  unfold gridLabel
  push_cast
  have h1 := abs_sub_round (x / (6 * h))
  have e : h * (6 * (round (x / (6 * h)) : ℝ)) - x = 6 * h * ((round (x / (6 * h)) : ℝ) -
      x / (6 * h)) := by field_simp
  rw [e, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  nlinarith

theorem six_dvd_gridLabel (h x : ℝ) : (6 : ℤ) ∣ gridLabel h x := ⟨_, rfl⟩

theorem round_err {h : ℝ} (hh : 0 < h) (x : ℝ) : |h * round (x / h) - x| ≤ h / 2 := by
  have h1 := abs_sub_round (x / h)
  have e : h * (round (x / h) : ℝ) - x = h * ((round (x / h) : ℝ) - x / h) := by field_simp
  rw [e, abs_mul, abs_of_pos hh, abs_sub_comm]
  nlinarith

/-- Equal grid labels force close labels: `|x - y| ≤ 6h`. -/
theorem gridLabel_close {h : ℝ} (hh : 0 < h) {x y : ℝ} (hxy : gridLabel h x = gridLabel h y) :
    |x - y| ≤ 6 * h := by
  have h1 := gridLabel_err hh x
  have h2 := gridLabel_err hh y
  rw [hxy] at h1
  calc |x - y| = |(h * gridLabel h y - y) - (h * gridLabel h y - x)| := by ring_nf
    _ ≤ |h * gridLabel h y - y| + |h * gridLabel h y - x| := abs_sub _ _
    _ ≤ 6 * h := by linarith

/-- The pure-shift error of rounded frequencies: `|h n·ζ' - n·ζ| ≤ d Q h / 2`. -/
theorem shift_round_err {d : ℕ} {h Q : ℝ} (hh : 0 < h) (ζ : Fin d → ℝ) (n : Fin d → ℤ)
    (hn : ∀ k, |(n k : ℝ)| ≤ Q) :
    |h * (shiftDot n (fun k => round (ζ k / h)) : ℝ) - ∑ k, (n k : ℝ) * ζ k| ≤ d * Q * h / 2 := by
  unfold shiftDot
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ k, (h * ((n k : ℝ) * (round (ζ k / h) : ℝ)) - (n k : ℝ) * ζ k)|
      ≤ ∑ k, |h * ((n k : ℝ) * (round (ζ k / h) : ℝ)) - (n k : ℝ) * ζ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, Q * (h / 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have e : h * ((n k : ℝ) * (round (ζ k / h) : ℝ)) - (n k : ℝ) * ζ k =
            (n k : ℝ) * (h * round (ζ k / h) - ζ k) := by ring
        rw [e, abs_mul]
        exact mul_le_mul (hn k) (round_err hh (ζ k)) (abs_nonneg _)
          ((abs_nonneg _).trans (hn k))
    _ = d * Q * h / 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

theorem logb_scale_bound {y : ℝ} (hy : 0 ≤ y) :
    1 + Real.logb 2 (2 + 4 * y) ≤ 3 * (1 + Real.logb 2 (2 + y)) ∧
      0 ≤ 1 + Real.logb 2 (2 + 4 * y) := by
  have h1 : Real.logb 2 (2 + 4 * y) ≤ Real.logb 2 (4 * (2 + y)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have h2 : Real.logb 2 (4 * (2 + y)) = Real.logb 2 4 + Real.logb 2 (2 + y) :=
    Real.logb_mul (by norm_num) (by positivity)
  have h3 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have h4 : 0 ≤ Real.logb 2 (2 + y) := Real.logb_nonneg (by norm_num) (by linarith)
  have h5 : 0 ≤ Real.logb 2 (2 + 4 * y) := Real.logb_nonneg (by norm_num) (by linarith)
  constructor <;> linarith

theorem sparse_count_final_arith {X δ L μ ν M : ℝ} {d : ℕ} (hδ0 : 0 < δ) (hL : 1 ≤ L)
    (hμ : 0 < μ) (hν : 0 ≤ ν)
    (h : X ≤ 10 ^ 11 * (1 + Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * (2 * ν) / (μ / 2))) *
      ((⌊L⌋₊ : ℕ) : ℝ) ^ 12 * δ ^ (1 / 300 : ℝ) * M ^ 2) :
    X ≤ 3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * ν / μ)) * L ^ 12 *
      δ ^ (1 / 300 : ℝ) * M ^ 2 := by
  set y := ((d : ℝ) + 1) ^ 2 * ν / μ
  have hy : 0 ≤ y := by positivity
  have e1 : ((d : ℝ) + 1) ^ 2 * (2 * ν) / (μ / 2) = 4 * y := by
    simp only [y]; field_simp; ring
  rw [e1] at h
  obtain ⟨hℓ, hpos⟩ := logb_scale_bound hy
  have hfl : ((⌊L⌋₊ : ℕ) : ℝ) ^ 12 ≤ L ^ 12 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) 12
  have hδp : 0 ≤ δ ^ (1 / 300 : ℝ) := Real.rpow_nonneg hδ0.le _
  have h1 : (10 : ℝ) ^ 11 * (1 + Real.logb 2 (2 + 4 * y)) ≤
      10 ^ 11 * (3 * (1 + Real.logb 2 (2 + y))) :=
    mul_le_mul_of_nonneg_left hℓ (by norm_num)
  have h2 : 0 ≤ (10 : ℝ) ^ 11 * (3 * (1 + Real.logb 2 (2 + y))) :=
    le_trans (mul_nonneg (by norm_num) hpos) h1
  have h3 := mul_le_mul h1 hfl (pow_nonneg (Nat.cast_nonneg _) 12) h2
  have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hδp) (sq_nonneg M)
  refine h.trans (h4.trans (le_of_eq ?_))
  ring



end TrilinearHT.Auto
end
