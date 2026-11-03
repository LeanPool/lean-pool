/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec111bDelayedMoments.Setup

/-!
# Trilinear Hilbert transform: delay_rows_sum
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def DelayRowsSumHcellStatement : Prop :=
  ∀ (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (θ : ℤ × ℤ → ℝ → ℂ)
    (L : ℝ)
    (_ : (0 : ℝ) ≤ L)
    (_ : ∀ I ∈ S, Continuous (θ I))
    (_ : ∀ I ∈ S, ∀ (y : ℝ), ‖θ I y‖ ≤ L)
    (_ : ∀ I ∈ S, ∀ (y z : ℝ), ‖θ I y - θ I z‖ ≤ L / dyadicGridLength G I.1 * |y - z|)
    (Dg : ℤ → ℝ → ℂ)
    (μg : ℤ → ℝ → ℂ)
    (e : ℤ → ℝ → ℝ)
    (ε : ℝ)
    (_ : (0 : ℝ) ≤ ε)
    (_ : ε ≤ (1 : ℝ))
    (N : ℤ)
    (K₀ : ℕ)
    (_ : ∀ I ∈ S, ∀ (h : ℤ), MemLp (Dg h) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ I ∈ S, ∀ (h : ℤ), MemLp (μg h) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ I ∈ S, ∀ (j : ℕ), I.1 + (↑j : ℤ) ≤ N → ∀ Q ∈ dyadicGeneration G I j, ∀ y ∈
      dyadicGridCell G Q.1 Q.2, ∀ z ∈ dyadicGridCell G Q.1 Q.2, μg (I.1 + (↑j : ℤ)) y =
      μg (I.1 + (↑j : ℤ)) z)
    (_ : ∀ I ∈ S, ∀ (j : ℕ), I.1 + (↑j : ℤ) ≤ N → ∀ Q ∈ dyadicGeneration G I j, ∫ (y : ℝ) in
      dyadicGridCell G Q.1 Q.2, Dg (I.1 + (↑j : ℤ)) y = ∫ (y : ℝ) in dyadicGridCell G
      Q.1 Q.2, μg (I.1 + (↑j : ℤ)) y)
    (_ : ∀ (h : ℤ), IntegrableOn (e h) (dyadicGridCell G J.1 J.2) volume)
    (_ : ∀ I ∈ S, ∀ (h : ℤ), I.1 ≤ h → h < N → ∀ᵐ (y : ℝ) ∂volume.restrict (dyadicGridCell G
      I.1 I.2), ‖Dg h y - Dg (h + (1 : ℤ)) y‖ ^ (2 : ℕ) ≤ e h y)
    (_ : ∀ I ∈ S, ∀ (h : ℤ), I.1 ≤ h → h < N → ∀ᵐ (y : ℝ) ∂volume.restrict (dyadicGridCell G
      I.1 I.2), ‖μg (h + (1 : ℤ)) y - μg h y‖ ^ (2 : ℕ) ≤ ε * e h y)
    (m : ℝ → ℝ)
    (_ : ∀ (y : ℝ), (0 : ℝ) ≤ m y)
    (_ : ∀ I ∈ S, ∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖Dg N y‖ ^ (2 : ℕ) ≤ (4 : ℝ) * ∫ (y
      : ℝ) in dyadicGridCell G I.1 I.2, m y),
  let dI : ℤ × ℤ → ℕ :=
    fun (I : ℤ × ℤ) => (N - I.1 - (↑K₀ : ℤ)).toNat
  ∀ (_ : ∀ I ∈ S, I.1 + (↑(K₀ + dI I) : ℤ) = N),
  let dmax : ℕ :=
    S.sup dI
  ∀ (_ : ∀ I ∈ S, dI I ≤ dmax),
  let α : ℤ × ℤ → ℕ → ℝ :=
    fun (I : ℤ × ℤ) (j : ℕ) => √(∫ (y : ℝ) in dyadicGridCell G I.1 I.2, e (I.1 + (↑j :
      ℤ)) y)
  ∀ (_ : ∀ (I : ℤ × ℤ) (j : ℕ), (0 : ℝ) ≤ α I j),
  let st : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, μg (I.1 + (↑K₀ : ℤ)) y *
      θ I y‖
  ∀ (_ : st = fun (I : ℤ × ℤ) => ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, μg (I.1 + (↑K₀ : ℤ))
      y * θ I y‖),
  let c : ℕ → ℝ :=
    fun (j : ℕ) => (4 : ℝ) * L * (2 : ℝ)⁻¹ ^ j
  ∀ (_ : c = fun (j : ℕ) => (4 : ℝ) * L * (2 : ℝ)⁻¹ ^ j)
    (_ : ∀ (j : ℕ), (0 : ℝ) ≤ c j),
  let ρ : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => (4 : ℝ)⁻¹ ^ (K₀ + dI I) * ∫ (y : ℝ) in dyadicGridCell G I.1 I.2,
      m y
  ∀ (_ : ρ = fun (I : ℤ × ℤ) => (4 : ℝ)⁻¹ ^ (K₀ + dI I) * ∫ (y : ℝ) in dyadicGridCell G I.1
      I.2, m y),
  ∀ I ∈ S, (dyadicGridLength G I.1)⁻¹ * ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, Dg
    (I.1 + (↑K₀ : ℤ)) y * θ I y‖ ^ (2 : ℕ) ≤ (3 : ℝ) * ((dyadicGridLength G I.1)⁻¹ *
    st I ^ (2 : ℕ)) + (3 : ℝ) * (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ (2 :
    ℕ) + (3 : ℝ) * ((4 : ℝ) * L ^ (2 : ℕ) * ρ I)


open scoped Classical in
private def DelayRowsSumStage1Statement : Prop :=
  ∀ (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (θ : ℤ × ℤ → ℝ → ℂ)
    (L : ℝ)
    (Dg : ℤ → ℝ → ℂ)
    (μg : ℤ → ℝ → ℂ)
    (e : ℤ → ℝ → ℝ)
    (E : ℝ)
    (N : ℤ)
    (K₀ : ℕ)
    (_ : ∀ I ∈ S, I.1 + (↑K₀ : ℤ) ≤ N)
    (_ : ∀ (h : ℤ) (y : ℝ), (0 : ℝ) ≤ e h y)
    (_ : ∀ (h : ℤ), IntegrableOn (e h) (dyadicGridCell G J.1 J.2) volume)
    (_ : ∀ (Hs : Finset ℤ), ∑ h ∈ Hs, ∫ (y : ℝ) in dyadicGridCell G J.1 J.2, e h y ≤ E)
    (m : ℝ → ℝ)
    (_ : ∀ (y : ℝ), (0 : ℝ) ≤ m y)
    (_ : IntegrableOn m (dyadicGridCell G J.1 J.2) volume)
    (_ : ∫ (y : ℝ) in dyadicGridCell G J.1 J.2, m y ≤ E)
    (_ : (0 : ℝ) ≤ E),
  let dI : ℤ × ℤ → ℕ :=
    fun (I : ℤ × ℤ) => (N - I.1 - (↑K₀ : ℤ)).toNat
  ∀ (_ : dI = fun (I : ℤ × ℤ) => (N - I.1 - (↑K₀ : ℤ)).toNat),
  let dmax : ℕ :=
    S.sup dI
  let α : ℤ × ℤ → ℕ → ℝ :=
    fun (I : ℤ × ℤ) (j : ℕ) => √(∫ (y : ℝ) in dyadicGridCell G I.1 I.2, e (I.1 + (↑j :
      ℤ)) y)
  ∀ (_ : α = fun (I : ℤ × ℤ) (j : ℕ) => √(∫ (y : ℝ) in dyadicGridCell G I.1 I.2, e (I.1 + (↑j
      : ℤ)) y)),
  let st : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, μg (I.1 + (↑K₀ : ℤ)) y *
      θ I y‖
  ∀ (_ : st = fun (I : ℤ × ℤ) => ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, μg (I.1 + (↑K₀ : ℤ))
      y * θ I y‖),
  let c : ℕ → ℝ :=
    fun (j : ℕ) => (4 : ℝ) * L * (2 : ℝ)⁻¹ ^ j
  ∀ (_ : ∀ (j : ℕ), (0 : ℝ) ≤ c j)
    (_ : ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j ≤ (8 : ℝ) * L * (2 : ℝ)⁻¹ ^ K₀),
  let ρ : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => (4 : ℝ)⁻¹ ^ (K₀ + dI I) * ∫ (y : ℝ) in dyadicGridCell G I.1 I.2,
      m y
  ∀ (_ : ρ = fun (I : ℤ × ℤ) => (4 : ℝ)⁻¹ ^ (K₀ + dI I) * ∫ (y : ℝ) in dyadicGridCell G I.1
      I.2, m y)
    (_ : ∀ I ∈ S, (dyadicGridLength G I.1)⁻¹ * ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, Dg
      (I.1 + (↑K₀ : ℤ)) y * θ I y‖ ^ (2 : ℕ) ≤ (3 : ℝ) * ((dyadicGridLength G I.1)⁻¹ *
      st I ^ (2 : ℕ)) + (3 : ℝ) * (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ (2 :
      ℕ) + (3 : ℝ) * ((4 : ℝ) * L ^ (2 : ℕ) * ρ I)),
  ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ * ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, Dg
    (I.1 + (↑K₀ : ℤ)) y * θ I y‖ ^ (2 : ℕ) ≤ (3 : ℝ) * ∑ I ∈ S, (dyadicGridLength G
    I.1)⁻¹ * ‖∫ (y : ℝ) in dyadicGridCell G I.1 I.2, μg (I.1 + (↑K₀ : ℤ)) y * θ I y‖ ^
    (2 : ℕ) + (3 : ℝ) * ((9 : ℝ) * L * (2 : ℝ)⁻¹ ^ K₀) ^ (2 : ℕ) * E




private theorem delay_rows_sum_hcell : DelayRowsSumHcellStatement := by
  classical
  intro G J S hSJ θ L hL hθc hθb hLip Dg μg e ε hε0 hε1 N K₀ hD2 hμ2 hμc hDμ hei heD heμ m hm0 hDN
    dI hdIe dmax hdle α hα0 st hst c hc hc0 ρ hρ I hI
  set r := dyadicGridLength G I.1 with hr
  have hr0 : 0 < r := dyadicGridLength_pos G I.1
  have hT := delay_cell_telescope G I hL (hθc I hI) (hθb I hI) (hLip I hI)
    (fun j => Dg (I.1 + j)) (fun j => μg (I.1 + j)) (fun j => hD2 I hI _)
    (fun j => hμ2 I hI _) K₀ (dI I)
    (fun j hj => hμc I hI j (by have := hdIe I hI; push_cast at this ⊢; omega))
    (fun j hj => hDμ I hI j (by have := hdIe I hI; push_cast at this ⊢; omega))
  have heI : ∀ h, IntegrableOn (e h) (dyadicGridCell G I.1 I.2) := fun h =>
    (hei h).mono_set (hSJ I hI)
  have hcast : ∀ j : ℕ, I.1 + ((j + 1 : ℕ) : ℤ) = I.1 + j + 1 := fun j => by push_cast; ring
  have hjN : ∀ j : ℕ, j < K₀ + dI I → I.1 + j < N := fun j hj => by
    have := hdIe I hI; push_cast at this; omega
  have ha : ∀ j : ℕ, j < K₀ + dI I → Real.sqrt (∫ y in dyadicGridCell G I.1 I.2,
      ‖Dg (I.1 + j) y - Dg (I.1 + ((j + 1 : ℕ) : ℤ)) y‖ ^ 2) ≤ α I j := fun j hj => by
    have h := sqrt_setIntegral_le_of_le zero_le_one (heI (I.1 + j))
      (u := fun y => Dg (I.1 + j) y - Dg (I.1 + ((j + 1 : ℕ) : ℤ)) y)
      ((heD I hI (I.1 + j) (by omega) (hjN j hj)).mono fun y hy => by
        rw [hcast, one_mul]; exact hy)
    rwa [Real.sqrt_one, one_mul] at h
  have hb : ∀ j : ℕ, j < K₀ + dI I → Real.sqrt (∫ y in dyadicGridCell G I.1 I.2,
      ‖μg (I.1 + ((j + 1 : ℕ) : ℤ)) y - μg (I.1 + j) y‖ ^ 2) ≤ α I j := fun j hj => by
    have h := sqrt_setIntegral_le_of_le hε0 (heI (I.1 + j))
      (u := fun y => μg (I.1 + ((j + 1 : ℕ) : ℤ)) y - μg (I.1 + j) y)
      ((heμ I hI (I.1 + j) (by omega) (hjN j hj)).mono fun y hy => by
        rw [hcast]; exact hy)
    refine h.trans ?_
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hs1
  have hm : Real.sqrt (∫ y in dyadicGridCell G I.1 I.2,
      ‖Dg (I.1 + ((K₀ + dI I : ℕ) : ℤ)) y‖ ^ 2) ≤
      2 * Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, m y) := by
    rw [hdIe I hI]
    calc Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖Dg N y‖ ^ 2)
        ≤ Real.sqrt (4 * ∫ y in dyadicGridCell G I.1 I.2, m y) := Real.sqrt_le_sqrt (hDN I hI)
      _ = 2 * Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, m y) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hsr := Real.sqrt_pos.mpr hr0
  have hmI0 : 0 ≤ ∫ y in dyadicGridCell G I.1 I.2, m y := integral_nonneg hm0
  set! z := L * (2 : ℝ)⁻¹ ^ (K₀ + dI I) * (2 * Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, m y))
    with hz
  have hT' : ‖∫ y in dyadicGridCell G I.1 I.2, Dg (I.1 + K₀) y * θ I y‖ / Real.sqrt r ≤
      st I / Real.sqrt r + ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j + z := by
    rw [div_le_iff₀ hsr]
    have hsum : ∑ j ∈ Finset.Ico K₀ (K₀ + dI I), 2 * L * (2 : ℝ)⁻¹ ^ j * Real.sqrt r *
        (Real.sqrt (∫ y in dyadicGridCell G I.1 I.2,
          ‖Dg (I.1 + j) y - Dg (I.1 + ((j + 1 : ℕ) : ℤ)) y‖ ^ 2) +
         Real.sqrt (∫ y in dyadicGridCell G I.1 I.2,
          ‖μg (I.1 + ((j + 1 : ℕ) : ℤ)) y - μg (I.1 + j) y‖ ^ 2)) ≤
        (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) * Real.sqrt r := by
      calc _ ≤ ∑ j ∈ Finset.Ico K₀ (K₀ + dI I), c j * α I j * Real.sqrt r := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' := (Finset.mem_Ico.mp hj).2
            have hp : 0 ≤ 2 * L * (2 : ℝ)⁻¹ ^ j * Real.sqrt r := by positivity
            calc _ ≤ 2 * L * (2 : ℝ)⁻¹ ^ j * Real.sqrt r * (α I j + α I j) :=
                  mul_le_mul_of_nonneg_left (add_le_add (ha j hj') (hb j hj')) hp
              _ = c j * α I j * Real.sqrt r := by rw [hc]; ring
        _ = (∑ j ∈ Finset.Ico K₀ (K₀ + dI I), c j * α I j) * Real.sqrt r := by
            rw [Finset.sum_mul]
        _ ≤ (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) * Real.sqrt r := by
            refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Ico_subset_Ico le_rfl (by have := hdle I hI; omega))
              (fun j _ _ => mul_nonneg (hc0 j) (hα0 I j))) hsr.le
    have hrem : L * (2 : ℝ)⁻¹ ^ (K₀ + dI I) * Real.sqrt r *
        Real.sqrt (∫ y in dyadicGridCell G I.1 I.2,
          ‖Dg (I.1 + ((K₀ + dI I : ℕ) : ℤ)) y‖ ^ 2) ≤ z * Real.sqrt r := by
      have hp : 0 ≤ L * (2 : ℝ)⁻¹ ^ (K₀ + dI I) * Real.sqrt r := by positivity
      calc _ ≤ L * (2 : ℝ)⁻¹ ^ (K₀ + dI I) * Real.sqrt r *
            (2 * Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, m y)) :=
            mul_le_mul_of_nonneg_left hm hp
        _ = _ := by rw [hz]; ring
    have e1 : (st I / Real.sqrt r + ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j + z) *
        Real.sqrt r = st I + (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) * Real.sqrt r +
          z * Real.sqrt r := by field_simp
    rw [e1]
    simp only [hst]
    linarith
  have hx0 : 0 ≤ st I / Real.sqrt r := div_nonneg (norm_nonneg _) hsr.le
  have hy0 : 0 ≤ ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hc0 j) (hα0 I j)
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hlhs0 : 0 ≤ ‖∫ y in dyadicGridCell G I.1 I.2, Dg (I.1 + K₀) y * θ I y‖ /
      Real.sqrt r := div_nonneg (norm_nonneg _) hsr.le
  have hsq := pow_le_pow_left₀ hlhs0 hT' 2
  have h3 : (st I / Real.sqrt r + ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j + z) ^ 2 ≤
      3 * (st I / Real.sqrt r) ^ 2 +
        3 * (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ 2 + 3 * z ^ 2 := by
    nlinarith only [sq_nonneg (st I / Real.sqrt r - ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j),
      sq_nonneg (st I / Real.sqrt r - z),
      sq_nonneg (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j - z)]
  have hr2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have e2 : (‖∫ y in dyadicGridCell G I.1 I.2, Dg (I.1 + K₀) y * θ I y‖ /
      Real.sqrt r) ^ 2 = r⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, Dg (I.1 + K₀) y * θ I y‖ ^ 2 := by
    rw [div_pow, hr2]; ring
  have e3 : (st I / Real.sqrt r) ^ 2 = r⁻¹ * st I ^ 2 := by rw [div_pow, hr2]; ring
  have e4 : z ^ 2 = 4 * L ^ 2 * ρ I := by
    rw [hz, hρ, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hmI0, ← pow_mul,
      mul_comm (K₀ + dI I) 2, pow_mul]; norm_num; ring
  rw [e2] at hsq
  rw [e3, e4] at h3
  linarith
-- the tails



private theorem delay_rows_sum_stage_1 : DelayRowsSumStage1Statement := by
  classical
  intro G J S hSJ θ L Dg μg e E N K₀ hN he0 hei hE m hm0 hmi hmE hE0 dI hdI dmax α hα st hst c hc0
    hcs ρ hρ hcell
  have hcs2 : ∑ I ∈ S, (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ 2 ≤
      (8 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * E := by
    have hcsum0 : 0 ≤ ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j :=
      Finset.sum_nonneg fun j _ => hc0 j
    calc ∑ I ∈ S, (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ 2
        ≤ ∑ I ∈ S, (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j) *
            ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j ^ 2 :=
          Finset.sum_le_sum fun I _ => weighted_sq_sum_le _ c (α I) (fun j _ => hc0 j)
      _ = (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j) *
            ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * ∑ I ∈ S, α I j ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ ≤ (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j) *
            ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * E := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hcsum0
          refine mul_le_mul_of_nonneg_left ?_ (hc0 j)
          have he := sum_cells_energy_le G J S hSJ e he0 hei hE j
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun I hI => ?_)) he
          rw [hα]
          exact Real.sq_sqrt (integral_nonneg fun _ => he0 _ _)
      _ = (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j) ^ 2 * E := by rw [← Finset.sum_mul]; ring
      _ ≤ (8 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * E :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcsum0 hcs 2) hE0
  -- the stopping remainders
  have hρs : ∑ I ∈ S, ρ I ≤ 2 * (4 : ℝ)⁻¹ ^ K₀ * E := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image Prod.fst)
      (g := fun I : ℤ × ℤ => I.1) (fun I hI => Finset.mem_image_of_mem _ hI)]
    have hdep : ∀ s ∈ S.image Prod.fst, ∑ I ∈ S with I.1 = s, ρ I ≤
        (4 : ℝ)⁻¹ ^ K₀ * (2 : ℝ)⁻¹ ^ (N - s - K₀).toNat * E := by
      intro s hs
      obtain ⟨I₀, hI₀, rfl⟩ := Finset.mem_image.mp hs
      have hc' : ∀ I ∈ S.filter (fun I => I.1 = I₀.1), ρ I =
          (4 : ℝ)⁻¹ ^ (K₀ + dI I₀) * ∫ y in dyadicGridCell G I.1 I.2, m y := fun I hI => by
        rw [hρ]; simp only [hdI, (Finset.mem_filter.mp hI).2]
      rw [Finset.sum_congr rfl hc', ← Finset.mul_sum]
      have hJm := sum_depth_cells_le G J (S.filter (fun I => I.1 = I₀.1)) I₀.1
        (fun I hI => ⟨(Finset.mem_filter.mp hI).2, hSJ I (Finset.mem_filter.mp hI).1⟩)
        hm0 hmi
      have hpow : (4 : ℝ)⁻¹ ^ (K₀ + dI I₀) ≤ (4 : ℝ)⁻¹ ^ K₀ * (2 : ℝ)⁻¹ ^ dI I₀ := by
        rw [pow_add]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      calc (4 : ℝ)⁻¹ ^ (K₀ + dI I₀) *
            ∑ I ∈ S with I.1 = I₀.1, ∫ y in dyadicGridCell G I.1 I.2, m y
          ≤ (4 : ℝ)⁻¹ ^ K₀ * (2 : ℝ)⁻¹ ^ dI I₀ * E :=
            mul_le_mul hpow (hJm.trans hmE)
              (Finset.sum_nonneg fun I _ => integral_nonneg hm0) (by positivity)
        _ = _ := by simp only [hdI]
    refine (Finset.sum_le_sum hdep).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hg := sum_geom_inj_le (S.image Prod.fst) (fun s => (N - s - K₀).toNat)
      (fun x hx y hy h => by
        obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨I', hI', rfl⟩ := Finset.mem_image.mp hy
        have := hN I hI; have := hN I' hI'
        simp only at h; omega)
    calc (4 : ℝ)⁻¹ ^ K₀ * (∑ s ∈ S.image Prod.fst, (2 : ℝ)⁻¹ ^ (N - s - K₀).toNat) * E
        ≤ (4 : ℝ)⁻¹ ^ K₀ * 2 * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hE0
      _ = _ := by ring
  calc _ ≤ ∑ I ∈ S, (3 * ((dyadicGridLength G I.1)⁻¹ * st I ^ 2) +
        3 * (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ 2 +
        3 * (4 * L ^ 2 * ρ I)) := Finset.sum_le_sum hcell
    _ = 3 * ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ * st I ^ 2 +
        3 * ∑ I ∈ S, (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ 2 +
        12 * L ^ 2 * ∑ I ∈ S, ρ I := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ 3 * ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ * st I ^ 2 +
        3 * ((8 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * E) + 12 * L ^ 2 * (2 * (4 : ℝ)⁻¹ ^ K₀ * E) := by
      have := mul_le_mul_of_nonneg_left hρs (by positivity : (0 : ℝ) ≤ 12 * L ^ 2)
      linarith
    _ ≤ _ := by
      have h4 : (4 : ℝ)⁻¹ ^ K₀ = ((2 : ℝ)⁻¹ ^ K₀) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4]
      have : 0 ≤ L ^ 2 * ((2 : ℝ)⁻¹ ^ K₀) ^ 2 * E := by positivity
      simp only [hst]
      nlinarith only [hE0]


/-- Blueprint lem:delay, proof lines 1558–1559: the delayed rows `|I|^{-1/2} ∫_I D_{s+K₀} θ_I`
of all use cells, against arbitrary bumps, are controlled by the predictor start terms and the
geometrically decaying telescoping rows, `C 2^{-K₀} ‖F_a‖₂` (orthogonal increments summed over
disjoint cells of each depth). The telescoping is stopped at the depth `N ≥ s + K₀` of the
projection family; the terminal remainder costs `C 2^{s - N} ‖1_I F_a‖`. -/
theorem delay_rows_sum (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (hSJ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (θ : ℤ × ℤ → ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L) (hθc : ∀ I ∈ S, Continuous (θ I))
    (hθb : ∀ I ∈ S, ∀ y, ‖θ I y‖ ≤ L)
    (hLip : ∀ I ∈ S, ∀ y z, ‖θ I y - θ I z‖ ≤ L / dyadicGridLength G I.1 * |y - z|)
    (Dg μg : ℤ → ℝ → ℂ) (e : ℤ → ℝ → ℝ) {ε E : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (N : ℤ) (K₀ : ℕ) (hN : ∀ I ∈ S, I.1 + K₀ ≤ N)
    (hD2 : ∀ I ∈ S, ∀ h, MemLp (Dg h) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hμ2 : ∀ I ∈ S, ∀ h, MemLp (μg h) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hμc : ∀ I ∈ S, ∀ j : ℕ, I.1 + j ≤ N → ∀ Q ∈ dyadicGeneration G I j,
      ∀ y ∈ dyadicGridCell G Q.1 Q.2, ∀ z ∈ dyadicGridCell G Q.1 Q.2,
        μg (I.1 + j) y = μg (I.1 + j) z)
    (hDμ : ∀ I ∈ S, ∀ j : ℕ, I.1 + j ≤ N → ∀ Q ∈ dyadicGeneration G I j,
      ∫ y in dyadicGridCell G Q.1 Q.2, Dg (I.1 + j) y =
        ∫ y in dyadicGridCell G Q.1 Q.2, μg (I.1 + j) y)
    (he0 : ∀ h y, 0 ≤ e h y) (hei : ∀ h, IntegrableOn (e h) (dyadicGridCell G J.1 J.2))
    (heD : ∀ I ∈ S, ∀ h, I.1 ≤ h → h < N → ∀ᵐ y ∂(volume.restrict (dyadicGridCell G I.1 I.2)),
      ‖Dg h y - Dg (h + 1) y‖ ^ 2 ≤ e h y)
    (heμ : ∀ I ∈ S, ∀ h, I.1 ≤ h → h < N → ∀ᵐ y ∂(volume.restrict (dyadicGridCell G I.1 I.2)),
      ‖μg (h + 1) y - μg h y‖ ^ 2 ≤ ε * e h y)
    (hE : ∀ Hs : Finset ℤ, ∑ h ∈ Hs, ∫ y in dyadicGridCell G J.1 J.2, e h y ≤ E)
    (m : ℝ → ℝ) (hm0 : ∀ y, 0 ≤ m y) (hmi : IntegrableOn m (dyadicGridCell G J.1 J.2))
    (hmE : ∫ y in dyadicGridCell G J.1 J.2, m y ≤ E)
    (hDN : ∀ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, ‖Dg N y‖ ^ 2 ≤
      4 * ∫ y in dyadicGridCell G I.1 I.2, m y) :
    ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, Dg (I.1 + K₀) y * θ I y‖ ^ 2 ≤
      3 * ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, μg (I.1 + K₀) y * θ I y‖ ^ 2 +
      3 * (9 * L * (2 : ℝ)⁻¹ ^ K₀) ^ 2 * E := by
  classical
  have hE0 : 0 ≤ E := by simpa using hE ∅
  set! dI : ℤ × ℤ → ℕ := fun I => (N - I.1 - K₀).toNat with hdI
  have hdIe : ∀ I ∈ S, I.1 + ((K₀ + dI I : ℕ) : ℤ) = N := fun I hI => by
    have := hN I hI; simp only [hdI]; push_cast; omega
  set! dmax := S.sup dI with hdmax
  have hdle : ∀ I ∈ S, dI I ≤ dmax := fun I hI => Finset.le_sup (f := dI) hI
  set! α : ℤ × ℤ → ℕ → ℝ := fun I j =>
    Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, e (I.1 + j) y) with hα
  have hα0 : ∀ I j, 0 ≤ α I j := fun I j => Real.sqrt_nonneg _
  set! st : ℤ × ℤ → ℝ := fun I =>
    ‖∫ y in dyadicGridCell G I.1 I.2, μg (I.1 + K₀) y * θ I y‖ with hst
  set! c : ℕ → ℝ := fun j => 4 * L * (2 : ℝ)⁻¹ ^ j with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hcs : ∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j ≤ 8 * L * (2 : ℝ)⁻¹ ^ K₀ := by
    rw [hc, ← Finset.mul_sum]
    have := geom_Ico_le K₀ dmax
    nlinarith only [hL, this]
  set! ρ : ℤ × ℤ → ℝ := fun I => (4 : ℝ)⁻¹ ^ (K₀ + dI I) * ∫ y in dyadicGridCell G I.1 I.2, m y
    with hρ
  -- per cell
  have hcell : ∀ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
      ‖∫ y in dyadicGridCell G I.1 I.2, Dg (I.1 + K₀) y * θ I y‖ ^ 2 ≤
      3 * ((dyadicGridLength G I.1)⁻¹ * st I ^ 2) +
      3 * (∑ j ∈ Finset.Ico K₀ (K₀ + dmax), c j * α I j) ^ 2 + 3 * (4 * L ^ 2 * ρ I) := by
    expose_names
    exact @delay_rows_sum_hcell G J S hSJ θ L hL hθc hθb hLip Dg μg e ε hε0 hε1 N K₀ hD2 hμ2 hμc
      hDμ hei heD heμ m hm0 hDN hdIe hdle hα0 hst hc hc0 hρ
  expose_names
  exact @delay_rows_sum_stage_1 G J S hSJ θ L Dg μg e E N K₀ hN he0 hei hE m hm0 hmi hmE hE0 hdI
    hα hst hc0 hcs hρ hcell

/-- Blueprint lem:delay, proof line 1559: for mean-zero bumps the start term is
`∫_I (μ_H - μ_s) ω_I`, a sum of `K₀` private increments, costing `K₀ √ε ‖F_a‖₂`. -/
theorem delay_start_meanZero (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (hSJ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (θ : ℤ × ℤ → ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L) (hθc : ∀ I ∈ S, Continuous (θ I))
    (hθb : ∀ I ∈ S, ∀ y, ‖θ I y‖ ≤ L)
    (hθ0 : ∀ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, θ I y = 0)
    (μg : ℤ → ℝ → ℂ) (e : ℤ → ℝ → ℝ) {ε E : ℝ} (hε0 : 0 ≤ ε)
    (hμ2 : ∀ I ∈ S, ∀ h, MemLp (μg h) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hμI : ∀ I ∈ S, ∀ y ∈ dyadicGridCell G I.1 I.2, ∀ z ∈ dyadicGridCell G I.1 I.2,
      μg I.1 y = μg I.1 z)
    (he0 : ∀ h y, 0 ≤ e h y) (hei : ∀ h, IntegrableOn (e h) (dyadicGridCell G J.1 J.2))
    (N : ℤ) (K₀ : ℕ) (hN : ∀ I ∈ S, I.1 + K₀ ≤ N)
    (heμ : ∀ I ∈ S, ∀ h, I.1 ≤ h → h < N → ∀ᵐ y ∂(volume.restrict (dyadicGridCell G I.1 I.2)),
      ‖μg (h + 1) y - μg h y‖ ^ 2 ≤ ε * e h y)
    (hE : ∀ Hs : Finset ℤ, ∑ h ∈ Hs, ∫ y in dyadicGridCell G J.1 J.2, e h y ≤ E) :
    ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, μg (I.1 + K₀) y * θ I y‖ ^ 2 ≤
      (L * K₀) ^ 2 * ε * E := by
  classical
  have hE0 : 0 ≤ E := by simpa using hE ∅
  have hcell : ∀ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
      ‖∫ y in dyadicGridCell G I.1 I.2, μg (I.1 + K₀) y * θ I y‖ ^ 2 ≤
      L ^ 2 * (K₀ * ε * ∑ j ∈ Finset.range K₀,
        ∫ y in dyadicGridCell G I.1 I.2, e (I.1 + j) y) := by
    intro I hI
    set C := dyadicGridCell G I.1 I.2 with hC
    have := cell_isFiniteMeasure G I.1 I.2
    set r := dyadicGridLength G I.1 with hr
    have hr0 : 0 < r := dyadicGridLength_pos G I.1
    have hθm : Measurable (θ I) := (hθc I hI).measurable
    have heI : ∀ h, IntegrableOn (e h) C := fun h => (hei h).mono_set (hSJ I hI)
    -- the start term `∫ μ_s θ` vanishes
    have hconst : ∀ y ∈ C, μg I.1 y = μg I.1 (dyadicGridLeft G I.1 I.2) := fun y hy =>
      hμI I hI y hy _ (dyadicGridCell_left_mem G I.1 I.2)
    have hs : ∫ y in C, μg I.1 y * θ I y = 0 := by
      have h := setIntegral_mul_const_cell (G := G) (Q := I) hconst (θ I)
      simp_rw [mul_comm (μg I.1 _)]
      rw [h, hθ0 I hI, zero_mul]
    have h1 := integrableOn_cell_mul_bdd (I := I) (hμ2 I hI (I.1 + K₀)) hθm (hθb I hI)
    have h2 := integrableOn_cell_mul_bdd (I := I) (hμ2 I hI I.1) hθm (hθb I hI)
    have hsplit : ∫ y in C, μg (I.1 + K₀) y * θ I y =
        ∫ y in C, (μg (I.1 + K₀) y - μg I.1 y) * θ I y := by
      have h3 : ∫ y in C, (μg (I.1 + K₀) y - μg I.1 y) * θ I y =
          (∫ y in C, μg (I.1 + K₀) y * θ I y) - ∫ y in C, μg I.1 y * θ I y := by
        rw [← integral_sub h1 h2]; congr 1; funext y; ring
      rw [h3, hs, sub_zero]
    have hb := norm_setIntegral_cell_mul_le (I := I) ((hμ2 I hI (I.1 + K₀)).sub (hμ2 I hI I.1))
      hL (hθb I hI)
    -- the increments
    have hcast : ∀ j : ℕ, I.1 + ((j + 1 : ℕ) : ℤ) = I.1 + j + 1 := fun j => by push_cast; ring
    have hall : ∀ᵐ y ∂(volume.restrict C), ∀ j ∈ Finset.range K₀,
        ‖μg (I.1 + j + 1) y - μg (I.1 + j) y‖ ^ 2 ≤ ε * e (I.1 + j) y := by
      refine (Filter.eventually_all_finset _).mpr fun j hj => ?_
      have := hN I hI
      exact heμ I hI (I.1 + j) (by omega) (by have := Finset.mem_range.mp hj; omega)
    have hpt : ∀ᵐ y ∂(volume.restrict C), ‖μg (I.1 + K₀) y - μg I.1 y‖ ^ 2 ≤
        K₀ * ε * ∑ j ∈ Finset.range K₀, e (I.1 + j) y := by
      filter_upwards [hall] with y hy
      have htel := Finset.sum_range_sub (fun j : ℕ => μg (I.1 + j) y) K₀
      simp only [Nat.cast_zero, add_zero] at htel
      rw [← htel]
      calc ‖∑ j ∈ Finset.range K₀, (μg (I.1 + ((j + 1 : ℕ) : ℤ)) y - μg (I.1 + j) y)‖ ^ 2
          ≤ (∑ j ∈ Finset.range K₀, ‖μg (I.1 + ((j + 1 : ℕ) : ℤ)) y - μg (I.1 + j) y‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ (Finset.range K₀).card *
            ∑ j ∈ Finset.range K₀, ‖μg (I.1 + ((j + 1 : ℕ) : ℤ)) y - μg (I.1 + j) y‖ ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ ≤ K₀ * ∑ j ∈ Finset.range K₀, ε * e (I.1 + j) y := by
            rw [Finset.card_range]
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
            rw [hcast]; exact hy j hj
        _ = K₀ * ε * ∑ j ∈ Finset.range K₀, e (I.1 + j) y := by rw [← Finset.mul_sum]; ring
    have hint : ∫ y in C, ‖μg (I.1 + K₀) y - μg I.1 y‖ ^ 2 ≤
        K₀ * ε * ∑ j ∈ Finset.range K₀, ∫ y in C, e (I.1 + j) y := by
      rw [← integral_finsetSum _ (fun j _ => heI _), ← integral_const_mul]
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
        ((integrable_finsetSum _ (fun j _ => heI _)).const_mul _) hpt
    have hX0 : 0 ≤ ∫ y in C, ‖μg (I.1 + K₀) y - μg I.1 y‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    rw [hsplit]
    have hb' : ‖∫ y in C, (μg (I.1 + K₀) y - μg I.1 y) * θ I y‖ ^ 2 ≤
        (L * Real.sqrt r * Real.sqrt (∫ y in C, ‖μg (I.1 + K₀) y - μg I.1 y‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Pi.sub_apply] using hb) 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hr0.le, Real.sq_sqrt hX0] at hb'
    calc r⁻¹ * ‖∫ y in C, (μg (I.1 + K₀) y - μg I.1 y) * θ I y‖ ^ 2
        ≤ r⁻¹ * (L ^ 2 * r * ∫ y in C, ‖μg (I.1 + K₀) y - μg I.1 y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = L ^ 2 * ∫ y in C, ‖μg (I.1 + K₀) y - μg I.1 y‖ ^ 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)
  calc _ ≤ ∑ I ∈ S, L ^ 2 * (K₀ * ε * ∑ j ∈ Finset.range K₀,
        ∫ y in dyadicGridCell G I.1 I.2, e (I.1 + j) y) := Finset.sum_le_sum hcell
    _ = L ^ 2 * K₀ * ε * ∑ j ∈ Finset.range K₀,
        ∑ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, e (I.1 + j) y := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun I _ => by ring
    _ ≤ L ^ 2 * K₀ * ε * ∑ j ∈ Finset.range K₀, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
        sum_cells_energy_le G J S hSJ e he0 hei hE j) (by positivity)
    _ = (L * K₀) ^ 2 * ε * E := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The start term for general bumps: `Σ_I |I|⁻¹ |∫_I μ_H θ_I|² ≤ L² Σ_I ‖1_I μ_H‖²`. -/
theorem delay_start_depth (G : RealDyadicGrid) (S : Finset (ℤ × ℤ))
    (θ : ℤ × ℤ → ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L) (hθb : ∀ I ∈ S, ∀ y, ‖θ I y‖ ≤ L)
    (μ : ℝ → ℂ) (hμ2 : ∀ I ∈ S, MemLp μ 2 (volume.restrict (dyadicGridCell G I.1 I.2))) :
    ∑ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
        ‖∫ y in dyadicGridCell G I.1 I.2, μ y * θ I y‖ ^ 2 ≤
      L ^ 2 * ∑ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, ‖μ y‖ ^ 2 := by
  have hcell : ∀ I ∈ S, (dyadicGridLength G I.1)⁻¹ *
      ‖∫ y in dyadicGridCell G I.1 I.2, μ y * θ I y‖ ^ 2 ≤
      L ^ 2 * ∫ y in dyadicGridCell G I.1 I.2, ‖μ y‖ ^ 2 := by
    intro I hI
    have hr0 := dyadicGridLength_pos G I.1
    have hb := norm_setIntegral_cell_mul_le (I := I) (hμ2 I hI) hL (hθb I hI)
    have hX0 : 0 ≤ ∫ y in dyadicGridCell G I.1 I.2, ‖μ y‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    have hb' := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hr0.le, Real.sq_sqrt hX0] at hb'
    calc _ ≤ (dyadicGridLength G I.1)⁻¹ * (L ^ 2 * dyadicGridLength G I.1 *
          ∫ y in dyadicGridCell G I.1 I.2, ‖μ y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = _ := by field_simp
  calc _ ≤ ∑ I ∈ S, L ^ 2 * ∫ y in dyadicGridCell G I.1 I.2, ‖μ y‖ ^ 2 :=
        Finset.sum_le_sum hcell
    _ = _ := by rw [Finset.mul_sum]

/-- A compactly supported `C²` bump on `[a₀, a₀ + r)` has `‖f'‖ ≤ 2 r sup ‖f''‖`. -/
theorem norm_deriv_le_of_support {f : ℝ → ℂ} {a₀ r B : ℝ} (hr : 0 < r) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ y, y ∉ Set.Ico a₀ (a₀ + r) → f y = 0) (hB : ∀ y, ‖deriv (deriv f) y‖ ≤ B)
    (y : ℝ) : ‖deriv f y‖ ≤ 2 * r * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hd1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdd : ∀ x, DifferentiableAt ℝ (deriv f) x := fun x =>
    (hd1.differentiable one_ne_zero) x
  -- the derivative vanishes off the closed support interval
  have hzero : ∀ x, (x < a₀ ∨ a₀ + r < x) → deriv f x = 0 := by
    intro x hx
    have hev : f =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      rcases hx with hx | hx
      · filter_upwards [Iio_mem_nhds hx] with u hu
        exact hsupp u (fun h => absurd h.1 (not_le.mpr hu))
      · filter_upwards [Ioi_mem_nhds hx] with u hu
        exact hsupp u (fun h => absurd h.2 (not_lt.mpr (le_of_lt hu)))
    rw [hev.deriv_eq]; simp
  by_cases hy : y < a₀ ∨ a₀ + r < y
  · rw [hzero y hy, norm_zero]; positivity
  push Not at hy
  have hz : deriv f (a₀ - r) = 0 := hzero _ (Or.inl (by linarith))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun x _ => hdd x)
    (fun x _ => hB x) convex_univ (Set.mem_univ (a₀ - r)) (Set.mem_univ y)
  rw [hz, sub_zero, Real.norm_eq_abs] at h
  refine h.trans ?_
  have : |y - (a₀ - r)| ≤ 2 * r := by rw [abs_le]; constructor <;> linarith
  nlinarith

/-- The Lipschitz bound `‖f y - f z‖ ≤ 2 r B |y - z|` for such bumps. -/
theorem lipschitz_of_support {f : ℝ → ℂ} {a₀ r B : ℝ} (hr : 0 < r) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ y, y ∉ Set.Ico a₀ (a₀ + r) → f y = 0) (hB : ∀ y, ‖deriv (deriv f) y‖ ≤ B)
    (y z : ℝ) : ‖f y - f z‖ ≤ 2 * r * B * |y - z| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun x _ => (hf.differentiable (by norm_num)) x)
    (fun x _ => norm_deriv_le_of_support hr hf hsupp hB x) convex_univ (Set.mem_univ z)
    (Set.mem_univ y)
  rwa [Real.norm_eq_abs] at h

/-- The modulated class wave `θ(y) = W(y) e(c y)` is bounded by two and Lipschitz with constant
`(2A + 4π r |c|)/r`. -/
theorem classWave_mod_bounds (κ : LocalKernelClass) {a₀ r : ℝ} (hr : 0 < r) (α c : ℝ) {A : ℝ}
    (hA : 2 * (kernelPlateau κ).K * (1 + 6 * Real.pi * (r * |α|)) ^ 2 ≤ A) :
    Continuous (fun y => classWave κ a₀ r α y * (Real.fourierChar (c * y) : ℂ)) ∧
    (∀ y, ‖classWave κ a₀ r α y * (Real.fourierChar (c * y) : ℂ)‖ ≤ 2) ∧
    ∀ y z, ‖classWave κ a₀ r α y * (Real.fourierChar (c * y) : ℂ) -
        classWave κ a₀ r α z * (Real.fourierChar (c * z) : ℂ)‖ ≤
      (2 * A + 4 * Real.pi * (r * |c|)) / r * |y - z| := by
  obtain ⟨hs, hsupp, -, hb, -⟩ := classWave_props κ (a₀ := a₀) hr α
  have hd2 := classWave_deriv2_le κ (a₀ := a₀) hr α hA
  have hEc : Continuous (fun y : ℝ => (Real.fourierChar (c * y) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_const.mul continuous_id))
  refine ⟨hs.continuous.mul hEc, fun y => ?_, fun y z => ?_⟩
  · rw [norm_mul, Circle.norm_coe, mul_one]; exact hb y
  · have hL := lipschitz_of_support hr (hs.of_le (by simp)) hsupp hd2 y z
    have hE := norm_fourierChar_sub_le (c * y) (c * z)
    have e : classWave κ a₀ r α y * (Real.fourierChar (c * y) : ℂ) -
        classWave κ a₀ r α z * (Real.fourierChar (c * z) : ℂ) =
        (classWave κ a₀ r α y - classWave κ a₀ r α z) * (Real.fourierChar (c * y) : ℂ) +
          classWave κ a₀ r α z * ((Real.fourierChar (c * y) : ℂ) -
            (Real.fourierChar (c * z) : ℂ)) := by ring
    rw [e]
    have h1 : ‖(classWave κ a₀ r α y - classWave κ a₀ r α z) *
        (Real.fourierChar (c * y) : ℂ)‖ ≤ 2 * r * (A / r ^ 2) * |y - z| := by
      rw [norm_mul, Circle.norm_coe, mul_one]; exact hL
    have h2 : ‖classWave κ a₀ r α z * ((Real.fourierChar (c * y) : ℂ) -
        (Real.fourierChar (c * z) : ℂ))‖ ≤ 2 * (2 * Real.pi * (|c| * |y - z|)) := by
      rw [norm_mul]
      refine mul_le_mul (hb z) ?_ (norm_nonneg _) (by norm_num)
      rw [← mul_sub, abs_mul] at hE; exact hE
    have e2 : 2 * r * (A / r ^ 2) * |y - z| + 2 * (2 * Real.pi * (|c| * |y - z|)) =
        (2 * A + 4 * Real.pi * (r * |c|)) / r * |y - z| := by
      field_simp; ring
    rw [← e2]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem bumpMultiplier_le_small {η : ℝ} (h : |η| ≤ 1) :
    bumpMultiplier η ≤ (2 * Real.pi) ^ 2 * |η| := by
  unfold bumpMultiplier
  simp only [h, ↓reduceIte]
  rw [mul_pow, ← sq_abs η]
  have : |η| ^ 2 ≤ |η| := by nlinarith [abs_nonneg η]
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem bumpMultiplier_le_large {η : ℝ} (h : 1 < |η|) :
    bumpMultiplier η ≤ (2 * Real.pi) ^ 2 * |η|⁻¹ := by
  unfold bumpMultiplier
  have hn : ¬ |η| ≤ 1 := not_le.mpr h
  simp only [hn, ↓reduceIte]
  set p := 2 * Real.pi with hp
  set u := |η| with hu
  have hp1 : 1 ≤ p := by rw [hp]; nlinarith [Real.pi_gt_three]
  have hu0 : 0 < u := by linarith
  have e : (p * η) ^ 2 = p ^ 2 * u ^ 2 := by rw [mul_pow, hu, sq_abs]
  rw [e, inv_pow]
  have hp2 : 1 ≤ p ^ 2 := one_le_pow₀ hp1
  have h1 : u ≤ (p ^ 2 * u ^ 2) ^ 2 := by
    have h2 : u ^ 2 ≤ p ^ 2 * u ^ 2 := le_mul_of_one_le_left (by positivity) hp2
    have h3 : u ≤ u ^ 2 := by nlinarith
    have h4 : u ^ 2 ≤ (u ^ 2) ^ 2 := by nlinarith
    calc u ≤ (u ^ 2) ^ 2 := h3.trans h4
      _ ≤ (p ^ 2 * u ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  calc ((p ^ 2 * u ^ 2) ^ 2)⁻¹ ≤ u⁻¹ := inv_anti₀ hu0 h1
    _ ≤ p ^ 2 * u⁻¹ := le_mul_of_one_le_left (by positivity) hp2

/-- The multiplicity of a fixed center over distinct depths: the band multipliers at the
scales `|I_s| x` of a set of distinct depths sum to at most `4 (2π)²`. -/
theorem bumpMultiplier_depth_sum_le (G : RealDyadicGrid) (Ds : Finset ℤ) (x : ℝ) :
    ∑ s ∈ Ds, bumpMultiplier (dyadicGridLength G s * x) ≤ 4 * (2 * Real.pi) ^ 2 := by
  classical
  set c := (2 * Real.pi) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set small := Ds.filter (fun s => |dyadicGridLength G s * x| ≤ 1) with hsmall
  set large := Ds.filter (fun s => ¬ |dyadicGridLength G s * x| ≤ 1) with hlarge
  rw [← Finset.sum_filter_add_sum_filter_not Ds (fun s => |dyadicGridLength G s * x| ≤ 1)]
  have hlen : ∀ s (k : ℕ), dyadicGridLength G (s + k) = dyadicGridLength G s * (2 : ℝ)⁻¹ ^ k :=
    dyadicGridLength_add_nat G
  have hS : ∑ s ∈ small, bumpMultiplier (dyadicGridLength G s * x) ≤ 2 * c := by
    rcases small.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; positivity
    set s₀ := small.min' hne
    have hs₀ : s₀ ∈ small := small.min'_mem hne
    have hle : ∀ s ∈ small, s₀ ≤ s := fun s hs => small.min'_le s hs
    have hb : ∀ s ∈ small, bumpMultiplier (dyadicGridLength G s * x) ≤
        c * (2 : ℝ)⁻¹ ^ (s - s₀).toNat := by
      intro s hs
      have h1 := (Finset.mem_filter.mp hs).2
      refine (bumpMultiplier_le_small h1).trans (mul_le_mul_of_nonneg_left ?_ hc0)
      have e : s = s₀ + ((s - s₀).toNat : ℕ) := by have := hle s hs; omega
      have h0 := (Finset.mem_filter.mp hs₀).2
      rw [e, hlen, mul_comm (dyadicGridLength G s₀), mul_assoc, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (s - s₀).toNat)]
      rw [← e]
      calc (2 : ℝ)⁻¹ ^ (s - s₀).toNat * |dyadicGridLength G s₀ * x|
          ≤ (2 : ℝ)⁻¹ ^ (s - s₀).toNat * 1 := mul_le_mul_of_nonneg_left h0 (by positivity)
        _ = _ := mul_one _
    calc ∑ s ∈ small, bumpMultiplier (dyadicGridLength G s * x)
        ≤ ∑ s ∈ small, c * (2 : ℝ)⁻¹ ^ (s - s₀).toNat := Finset.sum_le_sum hb
      _ = c * ∑ s ∈ small, (2 : ℝ)⁻¹ ^ (s - s₀).toNat := by rw [Finset.mul_sum]
      _ ≤ c * 2 := mul_le_mul_of_nonneg_left (sum_geom_inj_le small _ (fun a ha b hb h => by
          have := hle a ha; have := hle b hb; omega)) hc0
      _ = 2 * c := by ring
  have hL : ∑ s ∈ large, bumpMultiplier (dyadicGridLength G s * x) ≤ 2 * c := by
    rcases large.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; positivity
    set s₁ := large.max' hne
    have hs₁ : s₁ ∈ large := large.max'_mem hne
    have hge : ∀ s ∈ large, s ≤ s₁ := fun s hs => large.le_max' s hs
    have hb : ∀ s ∈ large, bumpMultiplier (dyadicGridLength G s * x) ≤
        c * (2 : ℝ)⁻¹ ^ (s₁ - s).toNat := by
      intro s hs
      have h1 := not_le.mp (Finset.mem_filter.mp hs).2
      refine (bumpMultiplier_le_large h1).trans (mul_le_mul_of_nonneg_left ?_ hc0)
      have h0 := not_le.mp (Finset.mem_filter.mp hs₁).2
      have e : s₁ = s + ((s₁ - s).toNat : ℕ) := by have := hge s hs; omega
      have h2 : |dyadicGridLength G s₁ * x| =
          (2 : ℝ)⁻¹ ^ (s₁ - s).toNat * |dyadicGridLength G s * x| := by
        conv_lhs => rw [e]
        rw [hlen, mul_comm (dyadicGridLength G s), mul_assoc, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (s₁ - s).toNat)]
      rw [h2] at h0
      have hpos : 0 < |dyadicGridLength G s * x| := by linarith
      rw [inv_le_iff_one_le_mul₀ hpos]
      linarith
    calc ∑ s ∈ large, bumpMultiplier (dyadicGridLength G s * x)
        ≤ ∑ s ∈ large, c * (2 : ℝ)⁻¹ ^ (s₁ - s).toNat := Finset.sum_le_sum hb
      _ = c * ∑ s ∈ large, (2 : ℝ)⁻¹ ^ (s₁ - s).toNat := by rw [Finset.mul_sum]
      _ ≤ c * 2 := mul_le_mul_of_nonneg_left (sum_geom_inj_le large _ (fun a ha b hb h => by
          have := hge a ha; have := hge b hb; omega)) hc0
      _ = 2 * c := by ring
  linarith

/-- The row form of `linear_phase_scale_sum`: the same bound holds whenever the two families
of mean-zero wave rows of the inputs obey the square-sum bounds that admissibility would give,
with arbitrary input sizes `Na`, `Nb` (blueprint lem:delay, line 1559, pairs delayed rows with
the opposing Bessel rows). -/
theorem linear_phase_scale_sum_rows (G : RealDyadicGrid) (κ : LocalKernelClass)
    {ι : Type} (cell : ι → ℤ × ℤ) (S : Finset ι)
    (w : ι → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G (cell I).1 (cell I).2)
      (dyadicGridLength G (cell I).1) (w I))
    {a b : Fin 4} (hab : a ≠ b) (γ : ι → ℝ)
    (hinj : Set.InjOn (fun I => (cell I, γ I / ((b : ℝ) - (a : ℝ)))) S)
    {ψa ψb : ℝ → ℂ} (hψam : Measurable ψa) (hψbm : Measurable ψb)
    (hψa : ∀ y, ‖ψa y‖ ≤ 1) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb Na Nb : ℝ} (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hNa0 : 0 ≤ Na) (hNb0 : 0 ≤ Nb)
    (hzam : ∀ I, Measurable (za I)) (hzbm : ∀ I, Measurable (zb I))
    (hzai : ∀ I ∈ S, IntegrableOn (za (cell I)) (dyadicGridCell G (cell I).1 (cell I).2))
    (hzbi : ∀ I ∈ S, IntegrableOn (zb (cell I)) (dyadicGridCell G (cell I).1 (cell I).2))
    {M : ℝ} (hM : ∀ ξ, ∑ p ∈ S.image (fun I => ((cell I).1, γ I / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G p.1 * (ξ - p.2)) ≤ M)
    (hxrow : ∀ v, ∑ I ∈ S, ‖∫ y, conj (waveRowTest G κ cell
        (fun I => slotPairFreqA a b (dyadicGridLength G (cell I).1) v)
        (fun I => -(γ I / ((b : ℝ) - (a : ℝ)))) ψa I y) * za (cell I) y‖ ^ 2 ≤
      Ka ^ 2 * (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M)) ^ 2 * Na ^ 2)
    (hyrow : ∀ v, ∑ I ∈ S, ‖∫ y, conj (waveRowTest G κ cell
        (fun I => slotPairFreqB a b (dyadicGridLength G (cell I).1) v)
        (fun I => γ I / ((b : ℝ) - (a : ℝ))) ψb I y) * zb (cell I) y‖ ^ 2 ≤
      Kb ^ 2 * (charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M)) ^ 2 * Nb ^ 2) :
    ∑ I ∈ S, dyadicGridLength G (cell I).1 *
      ‖separatedLocalForm (dyadicGridLength G (cell I).1) (w I)
        (fun t => (Real.fourierChar (γ I * t) : ℂ)) a b (fun y => ψa y * za (cell I) y)
        (fun y => ψb y * zb (cell I) y)‖ ≤
      linearScaleConst κ * M * Ka * Kb * Na * Nb := by
  classical
  have hM0 : 0 ≤ M := (Finset.sum_nonneg fun p _ => bumpMultiplier_nonneg _).trans (hM 0)
  have hLn : ∀ v : Fin 2 → ℤ, 0 ≤ frequencyLength v := frequencyLength_nonneg
  obtain ⟨E, hE⟩ : ∃ E, E = kernelPointEnvelope κ 7 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (kernelPlateau κ).K := ⟨_, rfl⟩
  -- the rows
  obtain ⟨αA, hαA⟩ : ∃ f : (Fin 2 → ℤ) → ι → ℝ,
      f = fun v I => slotPairFreqA a b (dyadicGridLength G (cell I).1) v := ⟨_, rfl⟩
  obtain ⟨αB, hαB⟩ : ∃ f : (Fin 2 → ℤ) → ι → ℝ,
      f = fun v I => slotPairFreqB a b (dyadicGridLength G (cell I).1) v := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ f : (Fin 2 → ℤ) → ι → ℝ, f = fun v I =>
      ‖∫ y, conj (waveRowTest G κ cell (αA v) (fun I => -(γ I / ((b : ℝ) - (a : ℝ)))) ψa I y) *
        za (cell I) y‖ :=
    ⟨_, rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ f : (Fin 2 → ℤ) → ι → ℝ, f = fun v I =>
      ‖∫ y, conj (waveRowTest G κ cell (αB v) (fun I => γ I / ((b : ℝ) - (a : ℝ))) ψb I y) *
        zb (cell I) y‖ :=
    ⟨_, rfl⟩
  have hx0 : ∀ v I, 0 ≤ x v I := fun v I => by rw [hx]; exact norm_nonneg _
  have hy0 : ∀ v I, 0 ≤ yv v I := fun v I => by rw [hyv]; exact norm_nonneg _
  have hAa : ∀ v, ∀ I ∈ S, 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G (cell I).1 * |αA v I|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ => by
    rw [hαA]
    exact charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G (cell I).1).le (abs_nonneg _))
      (slotPairFreqA_le hab (dyadicGridLength_pos G (cell I).1) v)
  have hAb : ∀ v, ∀ I ∈ S, 2 * (kernelPlateau κ).K *
      (1 + 6 * Real.pi * (dyadicGridLength G (cell I).1 * |αB v I|)) ^ 2 ≤
        charWaveConst κ (frequencyLength v) := fun v I _ => by
    rw [hαB]
    exact charWaveConst_ge κ (mul_nonneg (dyadicGridLength_pos G (cell I).1).le (abs_nonneg _))
      (slotPairFreqB_le hab (dyadicGridLength_pos G (cell I).1) v)
  have hMa := multiplicity_neg G cell S (fun I => γ I / ((b : ℝ) - (a : ℝ))) hM
  have hinjA : Set.InjOn (fun I => (cell I, -(γ I / ((b : ℝ) - (a : ℝ))))) S := by
    intro i hi j hj h
    simp only [Prod.mk.injEq, neg_inj] at h
    exact hinj hi hj (Prod.ext h.1 h.2)
  -- Bessel bound per character
  set! bd : (Fin 2 → ℤ) → ℝ := fun v =>
    charWaveConst κ (frequencyLength v) * 1 * Real.sqrt (2 * M) with hbd
  have hbd0 : ∀ v, 0 ≤ bd v := fun v => by
    have := two_le_charWaveConst κ (hLn v)
    simp only [hbd]; positivity
  have hxs : ∀ v, ∑ I ∈ S, x v I ^ 2 ≤ Ka ^ 2 * bd v ^ 2 * Na ^ 2 := fun v => by
    simp only [hx, hαA, hbd]; exact hxrow v
  have hys : ∀ v, ∑ I ∈ S, yv v I ^ 2 ≤ Kb ^ 2 * bd v ^ 2 * Nb ^ 2 := fun v => by
    simp only [hyv, hαB, hbd]; exact hyrow v
  have hsqrt : ∀ {K' t N : ℝ}, 0 ≤ K' → 0 ≤ t → 0 ≤ N →
      Real.sqrt (K' ^ 2 * t ^ 2 * N ^ 2) = K' * t * N := by
    intro K' t N h1 h2 h3
    rw [show K' ^ 2 * t ^ 2 * N ^ 2 = (K' * t * N) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hcs : ∀ v, ∑ I ∈ S, x v I * yv v I ≤ Ka * Kb * bd v ^ 2 * Na * Nb := by
    intro v
    refine (Real.sum_mul_le_sqrt_mul_sqrt S (x v) (yv v)).trans ?_
    calc Real.sqrt (∑ I ∈ S, x v I ^ 2) * Real.sqrt (∑ I ∈ S, yv v I ^ 2)
        ≤ Real.sqrt (Ka ^ 2 * bd v ^ 2 * Na ^ 2) * Real.sqrt (Kb ^ 2 * bd v ^ 2 * Nb ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt (hxs v)) (Real.sqrt_le_sqrt (hys v))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Ka * Kb * bd v ^ 2 * Na * Nb := by
          rw [hsqrt hKa (hbd0 v) hNa0, hsqrt hKb (hbd0 v) hNb0]; ring
  -- the majorant
  set! U : (Fin 2 → ℤ) → ℝ := fun v =>
    E * ((1 + frequencyLength v) ^ 7)⁻¹ * (Ka * Kb * bd v ^ 2 * Na * Nb) with hU
  set! C0 := E * ((2 + 2 * K) * 25) ^ 2 * 2 * M * Ka * Kb * Na * Nb with hC0
  have hUe : ∀ v, U v = C0 * ((1 + frequencyLength v) ^ 3)⁻¹ := by
    intro v
    have h1 : 0 < 1 + frequencyLength v := by linarith [hLn v]
    simp only [hU, hbd, hC0, charWaveConst, ← hK]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hUs : Summable U := by
    have := summable_frequency_weight_three.mul_left C0
    exact this.congr fun v => (hUe v).symm
  have hE0 : 0 ≤ E := by
    rw [hE]
    refine le_max_of_le_left ?_
    unfold kernelUnitEnvelope; have := kernelDerivBound_nonneg κ 0; positivity
  have hfs : ∀ I ∈ S, Summable (fun v =>
      E * ((1 + frequencyLength v) ^ 7)⁻¹ * (x v I * yv v I)) := by
    intro I hI
    refine Summable.of_nonneg_of_le
      (fun v => by have := hx0 v I; have := hy0 v I; have := hLn v; positivity)
      (fun v => ?_) hUs
    have h1 : x v I * yv v I ≤ ∑ K' ∈ S, x v K' * yv v K' :=
      Finset.single_le_sum (f := fun K' => x v K' * yv v K')
        (fun K' _ => mul_nonneg (hx0 v K') (hy0 v K')) hI
    exact mul_le_mul_of_nonneg_left (h1.trans (hcs v)) (by have := hLn v; positivity)
  have hd1 : |((b : ℝ) - (a : ℝ))⁻¹| ≤ 1 := by
    rw [abs_inv]; exact inv_le_one_of_one_le₀ (one_le_abs_fin_sub hab)
  have hcell : ∀ I ∈ S, dyadicGridLength G (cell I).1 * ‖separatedLocalForm (dyadicGridLength G
      (cell I).1)
      (w I) (fun t => (Real.fourierChar (γ I * t) : ℂ)) a b (fun y => ψa y * za (cell I) y)
        (fun y => ψb y * zb (cell I) y)‖ ≤
      ∑' v, E * ((1 + frequencyLength v) ^ 7)⁻¹ * (x v I * yv v I) := by
    intro I hI
    have hr := dyadicGridLength_pos G (cell I).1
    have hwI := hw I hI
    rw [separatedLocalForm_indicator hr hwI]
    have hGa := integrable_cell_mul (dyadicGridCell_measurable G (cell I).1 (cell I).2)
      hψam hψa (hzam (cell I)) (hzai I hI)
    have hGb := integrable_cell_mul (dyadicGridCell_measurable G (cell I).1 (cell I).2)
      hψbm hψb (hzbm (cell I)) (hzbi I hI)
    have hGam := (hψam.mul (hzam (cell I))).indicator
      (dyadicGridCell_measurable G (cell I).1 (cell I).2)
    have hGbm := (hψbm.mul (hzbm (cell I))).indicator
      (dyadicGridCell_measurable G (cell I).1 (cell I).2)
    obtain ⟨hs, hb⟩ := separated_linear_cell_tensor hr hwI hab (γ I) hGam hGbm hGa hGb
    refine hb.trans ?_
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun v => ?_) (hs.mul_left _) (hfs I hI)
    have hXr : Real.sqrt (dyadicGridLength G (cell I).1)⁻¹ * ‖∫ y, classWave κ (dyadicGridLeft G
        (cell I).1 (cell I).2)
        (dyadicGridLength G (cell I).1) (slotPairFreqA a b (dyadicGridLength G (cell I).1) v) y *
        (Real.fourierChar ((-(γ I / ((b : ℝ) - (a : ℝ)))) * y) : ℂ) *
        (dyadicGridCell G (cell I).1 (cell I).2).indicator (ψa * za (cell I)) y‖ = x v I := by
      rw [show dyadicGridCell G (cell I).1 (cell I).2 = Set.Ico (dyadicGridLeft G (cell I).1 (cell
          I).2)
        (dyadicGridLeft G (cell I).1 (cell I).2 + dyadicGridLength G (cell I).1) from rfl,
        integral_classWave_indicator κ hr]
      simp only [hx, hαA, Pi.mul_apply]
      rw [integral_conj_waveRowTest, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      congr 3; funext y; ring
    have hYr : Real.sqrt (dyadicGridLength G (cell I).1)⁻¹ * ‖∫ y, classWave κ (dyadicGridLeft G
        (cell I).1 (cell I).2)
        (dyadicGridLength G (cell I).1) (slotPairFreqB a b (dyadicGridLength G (cell I).1) v) y *
        (Real.fourierChar ((γ I / ((b : ℝ) - (a : ℝ))) * y) : ℂ) *
        (dyadicGridCell G (cell I).1 (cell I).2).indicator (ψb * zb (cell I)) y‖ = yv v I := by
      rw [show dyadicGridCell G (cell I).1 (cell I).2 = Set.Ico (dyadicGridLeft G (cell I).1 (cell
          I).2)
        (dyadicGridLeft G (cell I).1 (cell I).2 + dyadicGridLength G (cell I).1) from rfl,
        integral_classWave_indicator κ hr]
      simp only [hyv, hαB, Pi.mul_apply]
      rw [integral_conj_waveRowTest, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      congr 3; funext y; ring
    simp only at hXr hYr ⊢
    rw [hXr, hYr]
    have hc := admissibleKernel_coeff_envelope hr hwI 7 v
    have hpos : 0 < (1 + frequencyLength v) ^ 7 := by have := hLn v; positivity
    have hc' : ‖periodicFourierCoeff (cubePeriodization (kernelUnitRescale
        (dyadicGridLeft G (cell I).1 (cell I).2) (dyadicGridLength G (cell I).1) (w I)) 16) v‖ ≤
        E * ((1 + frequencyLength v) ^ 7)⁻¹ := by
      rw [hE, ← div_eq_mul_inv, le_div_iff₀ hpos]; exact hc
    have hxy := mul_nonneg (hx0 v I) (hy0 v I)
    calc |((b : ℝ) - (a : ℝ))⁻¹| * (‖periodicFourierCoeff (cubePeriodization (kernelUnitRescale
          (dyadicGridLeft G (cell I).1 (cell I).2) (dyadicGridLength G (cell I).1) (w I)) 16) v‖ *
              x v I * yv v I)
        ≤ 1 * (‖periodicFourierCoeff (cubePeriodization (kernelUnitRescale
          (dyadicGridLeft G (cell I).1 (cell I).2) (dyadicGridLength G (cell I).1) (w I)) 16) v‖ *
              x v I * yv v I) :=
          mul_le_mul_of_nonneg_right hd1 (by rw [mul_assoc]; positivity)
      _ ≤ E * ((1 + frequencyLength v) ^ 7)⁻¹ * (x v I * yv v I) := by
          rw [one_mul, mul_assoc]; exact mul_le_mul_of_nonneg_right hc' hxy
  calc ∑ I ∈ S, dyadicGridLength G (cell I).1 * ‖separatedLocalForm (dyadicGridLength G (cell
      I).1) (w I)
        (fun t => (Real.fourierChar (γ I * t) : ℂ)) a b (fun y => ψa y * za (cell I) y)
        (fun y => ψb y * zb (cell I) y)‖
      ≤ ∑ I ∈ S, ∑' v, E * ((1 + frequencyLength v) ^ 7)⁻¹ * (x v I * yv v I) :=
        Finset.sum_le_sum hcell
    _ = ∑' v, ∑ I ∈ S, E * ((1 + frequencyLength v) ^ 7)⁻¹ * (x v I * yv v I) :=
        (Summable.tsum_finsetSum hfs).symm
    _ ≤ ∑' v, U v := by
        refine Summable.tsum_le_tsum (fun v => ?_) (summable_sum hfs) hUs
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hcs v) (by have := hLn v; positivity)
    _ = C0 * ∑' v : Fin 2 → ℤ, ((1 + frequencyLength v) ^ 3)⁻¹ := by
        rw [tsum_congr hUe, tsum_mul_left]
    _ = linearScaleConst κ * M * Ka * Kb * Na * Nb := by
        simp only [hC0, linearScaleConst, hE, hK]; ring


end TrilinearHT.Auto
end
