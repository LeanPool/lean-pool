/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLevelThreeSP

/-!
# The third level of the vorticity bootstrap

The second derivative of the vorticity flux is square integrable by the third-level product
bound; differentiating the weak heat equation of the first derivatives of the vorticity gives the
weak heat equation of the second derivatives (the third level of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The second derivative of the vorticity flux, `∂ₖ ∂ₘ(-(uⱼ ωᵢ - ωⱼ uᵢ))`. -/
@[expose] def vorticityFluxDeriv2 (U : Fin 3 → Vec3 × ℝ → ℝ) (G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (i j m k : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  -(((D2 j m k z * vorticityCurl G i z + G j m z * Ω1 i k z) +
      (G j k z * Ω1 i m z + U j z * Ω2 i m k z)) -
    ((Ω2 j m k z * U i z + Ω1 j m z * G i k z) +
      (Ω1 j k z * G i m z + vorticityCurl G j z * D2 i m k z)))

/-- The weak derivative of the flux derivative. -/
theorem vorticityFluxDeriv_weakDeriv {W : Set (Vec3 × ℝ)} (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict W)) (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict W))
    (hD2 : ∀ i j k, MemLp (D2 i j k) 2 (volume.restrict W))
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 (volume.restrict W))
    (hΩ2 : ∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict W))
    (hdU : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, U i y * spatialPartial ψ j y = -∫ y in W, G i j y * ψ y)
    (hdG : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, G i j y * spatialPartial ψ k y = -∫ y in W, D2 i j k y * ψ y)
    (hdw : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, vorticityCurl G i y * spatialPartial ψ j y = -∫ y in W, Ω1 i j y * ψ y)
    (hdΩ1 : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, Ω1 i j y * spatialPartial ψ k y = -∫ y in W, Ω2 i j k y * ψ y)
    (i j m k : Fin 3) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, vorticityFluxDeriv U G Ω1 i j m y * spatialPartial ψ k y =
        -∫ y in W, vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k y * ψ y := by
  have hw := vorticityCurl_memLp hG
  have hi : ∀ f g : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      MemLp g 2 (volume.restrict W) → IntegrableOn (fun y => f y * g y) W :=
    fun f g hf hg => hf.integrable_mul hg
  have pA := vorticity_weakPartial_mul hWo hWb (hG j m) (hw i) (hD2 j m k) (hΩ1 i k)
    (hdG j m k) (hdw i k)
  have pB := vorticity_weakPartial_mul hWo hWb (hU j) (hΩ1 i m) (hG j k) (hΩ2 i m k)
    (hdU j k) (hdΩ1 i m k)
  have pC := vorticity_weakPartial_mul hWo hWb (hΩ1 j m) (hU i) (hΩ2 j m k) (hG i k)
    (hdΩ1 j m k) (hdU i k)
  have pD := vorticity_weakPartial_mul hWo hWb (hw j) (hG i m) (hΩ1 j k) (hD2 i m k)
    (hdw j k) (hdG i m k)
  have sAB := vorticity_weakPartial_add (hi _ _ (hG j m) (hw i)) (hi _ _ (hU j) (hΩ1 i m))
    ((hi _ _ (hD2 j m k) (hw i)).add (hi _ _ (hG j m) (hΩ1 i k)))
    ((hi _ _ (hG j k) (hΩ1 i m)).add (hi _ _ (hU j) (hΩ2 i m k))) pA pB
  have sCD := vorticity_weakPartial_add (hi _ _ (hΩ1 j m) (hU i)) (hi _ _ (hw j) (hG i m))
    ((hi _ _ (hΩ2 j m k) (hU i)).add (hi _ _ (hΩ1 j m) (hG i k)))
    ((hi _ _ (hΩ1 j k) (hG i m)).add (hi _ _ (hw j) (hD2 i m k))) pC pD
  have hdiff := vorticity_weakPartial_sub
    ((hi _ _ (hG j m) (hw i)).add (hi _ _ (hU j) (hΩ1 i m)))
    ((hi _ _ (hΩ1 j m) (hU i)).add (hi _ _ (hw j) (hG i m)))
    (((hi _ _ (hD2 j m k) (hw i)).add (hi _ _ (hG j m) (hΩ1 i k))).add
      ((hi _ _ (hG j k) (hΩ1 i m)).add (hi _ _ (hU j) (hΩ2 i m k))))
    (((hi _ _ (hΩ2 j m k) (hU i)).add (hi _ _ (hΩ1 j m) (hG i k))).add
      ((hi _ _ (hΩ1 j k) (hG i m)).add (hi _ _ (hw j) (hD2 i m k)))) sAB sCD
  exact vorticity_weakPartial_neg hdiff

/-- The pointwise bound of the second flux derivative. -/
theorem vorticityFluxDeriv2_sq_le {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {M : ℝ} {z : Vec3 × ℝ} (hz : ∀ i, |U i z| ≤ M) (i j m k : Fin 3) :
    vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2 ≤
      64 * ((∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) *
        ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, D2 a b c z ^ 2) +
          ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2)) +
      16 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2 := by
  set S := ∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2 with hS
  set D := ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, D2 a b c z ^ 2 with hD
  set T := ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2 with hT
  set R := ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2 with hR
  have e2 : ∀ (f : Fin 3 → Fin 3 → ℝ) (a b : Fin 3),
      f a b ^ 2 ≤ ∑ a : Fin 3, ∑ b : Fin 3, f a b ^ 2 :=
    fun f a b => (Finset.single_le_sum (f := fun b => f a b ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, f a b ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a))
  have e3 : ∀ (f : Fin 3 → Fin 3 → Fin 3 → ℝ) (a b c : Fin 3),
      f a b c ^ 2 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f a b c ^ 2 := fun f a b c =>
    (e2 (fun b c => f a b c) b c).trans (Finset.single_le_sum
      (f := fun a => ∑ b : Fin 3, ∑ c : Fin 3, f a b c ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a))
  have hG2 : ∀ a b, G a b z ^ 2 ≤ S := fun a b => e2 (fun a b => G a b z) a b
  have hD2' : ∀ a b c, D2 a b c z ^ 2 ≤ D := fun a b c => e3 (fun a b c => D2 a b c z) a b c
  have hΩ1' : ∀ a b, Ω1 a b z ^ 2 ≤ T := fun a b => e2 (fun a b => Ω1 a b z) a b
  have hΩ2' : ∀ a b c, Ω2 a b c z ^ 2 ≤ R := fun a b c => e3 (fun a b c => Ω2 a b c z) a b c
  have hw : ∀ l, vorticityCurl G l z ^ 2 ≤ 2 * S := fun l => vorticityCurl_sq_le G z l
  have hU2 : ∀ l, U l z ^ 2 ≤ M ^ 2 := fun l => by
    have := hz l
    have h0 : 0 ≤ |U l z| := abs_nonneg _
    nlinarith only [this, h0, sq_abs (U l z)]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hpr : ∀ x y X Y : ℝ, x ^ 2 ≤ X → y ^ 2 ≤ Y → (x * y) ^ 2 ≤ X * Y := fun x y X Y hx hy => by
    rw [mul_pow]
    exact mul_le_mul hx hy (sq_nonneg _) ((sq_nonneg x).trans hx)
  have h2 : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
    nlinarith only [sq_nonneg (x - y)]
  have h2' : ∀ x y : ℝ, (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
    nlinarith only [sq_nonneg (x + y)]
  set A1 := D2 j m k z * vorticityCurl G i z
  set A2 := G j m z * Ω1 i k z
  set A3 := G j k z * Ω1 i m z
  set A4 := U j z * Ω2 i m k z
  set B1 := Ω2 j m k z * U i z
  set B2 := Ω1 j m z * G i k z
  set B3 := Ω1 j k z * G i m z
  set B4 := vorticityCurl G j z * D2 i m k z
  have bA1 : A1 ^ 2 ≤ D * (2 * S) := hpr _ _ _ _ (hD2' j m k) (hw i)
  have bA2 : A2 ^ 2 ≤ S * T := hpr _ _ _ _ (hG2 j m) (hΩ1' i k)
  have bA3 : A3 ^ 2 ≤ S * T := hpr _ _ _ _ (hG2 j k) (hΩ1' i m)
  have bA4 : A4 ^ 2 ≤ M ^ 2 * R := hpr _ _ _ _ (hU2 j) (hΩ2' i m k)
  have bB1 : B1 ^ 2 ≤ R * M ^ 2 := hpr _ _ _ _ (hΩ2' j m k) (hU2 i)
  have bB2 : B2 ^ 2 ≤ T * S := hpr _ _ _ _ (hΩ1' j m) (hG2 i k)
  have bB3 : B3 ^ 2 ≤ T * S := hpr _ _ _ _ (hΩ1' j k) (hG2 i m)
  have bB4 : B4 ^ 2 ≤ (2 * S) * D := hpr _ _ _ _ (hw j) (hD2' i m k)
  have hsplit : vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2 ≤
      8 * (A1 ^ 2 + A2 ^ 2 + A3 ^ 2 + A4 ^ 2) + 8 * (B1 ^ 2 + B2 ^ 2 + B3 ^ 2 + B4 ^ 2) := by
    have e : vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z =
        -(((A1 + A2) + (A3 + A4)) - ((B1 + B2) + (B3 + B4))) := rfl
    rw [e, neg_sq]
    have := h2' ((A1 + A2) + (A3 + A4)) ((B1 + B2) + (B3 + B4))
    have ha := h2 (A1 + A2) (A3 + A4)
    have hb := h2 (B1 + B2) (B3 + B4)
    have ha1 := h2 A1 A2
    have ha2 := h2 A3 A4
    have hb1 := h2 B1 B2
    have hb2 := h2 B3 B4
    linarith only [this, ha, hb, ha1, ha2, hb1, hb2]
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => sq_nonneg _
  nlinarith only [hsplit, bA1, bA2, bA3, bA4, bB1, bB2, bB3, bB4, hS0, hD0, hT0, hR0]

/-- Square integrability and the bound of the second flux derivative from the product bound. -/
theorem vorticityFluxDeriv2_memLp {μ : Measure (Vec3 × ℝ)} {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {M : ℝ} (hU : ∀ i, MemLp (U i) 2 μ) (hUb : ∀ᵐ z ∂μ, ∀ i, |U i z| ≤ M)
    (hG : ∀ i j, MemLp (G i j) 2 μ) (hD2 : ∀ i j k, MemLp (D2 i j k) 2 μ)
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 μ) (hΩ2 : ∀ i j k, MemLp (Ω2 i j k) 2 μ)
    (hSP : Integrable (fun y => (∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2) *
      ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k y ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j y ^ 2)) μ) (i j m k : Fin 3) :
    MemLp (vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k) 2 μ := by
  have hw := vorticityCurl_memLp hG
  have hmeas : AEStronglyMeasurable (vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k) μ := by
    have a : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 μ → AEStronglyMeasurable f μ :=
      fun f hf => hf.aestronglyMeasurable
    unfold vorticityFluxDeriv2
    exact ((((a _ (hD2 j m k)).mul (a _ (hw i))).add ((a _ (hG j m)).mul (a _ (hΩ1 i k)))).add
      (((a _ (hG j k)).mul (a _ (hΩ1 i m))).add ((a _ (hU j)).mul (a _ (hΩ2 i m k)))) |>.sub
      ((((a _ (hΩ2 j m k)).mul (a _ (hU i))).add ((a _ (hΩ1 j m)).mul (a _ (hG i k)))).add
      (((a _ (hΩ1 j k)).mul (a _ (hG i m))).add ((a _ (hw j)).mul (a _ (hD2 i m k)))))).neg
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have hR : Integrable (fun z => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2) μ :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun c _ =>
        (memLp_two_iff_integrable_sq (hΩ2 a b c).aestronglyMeasurable).1 (hΩ2 a b c)
  refine ((hSP.const_mul 64).add (hR.const_mul (16 * M ^ 2))).mono' (hmeas.pow 2) ?_
  filter_upwards [hUb] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact vorticityFluxDeriv2_sq_le hz i j m k

end ESS
