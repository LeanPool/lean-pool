/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBesselSteps
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBesselLower
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzMollifierFullBound

/-!
# The regularized bilinear tensor in even Bessel norms

On complex Schwartz data, the complete H²ᵏ norm of the regularized
bilinear tensor (J_ε g) ⊗ f is bounded by a fixed constant times the
L² norm of g and the complete H²ᵏ norm of f. The mollified factor
absorbs every derivative in the uniform norm, so no derivative of g
enters the estimate.
-/

public section

open MeasureTheory
open scoped ENNReal SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The regularized bilinear Schwartz tensor is bounded from
L² × H²ᵏ into the complete Bessel space H²ᵏ, with a constant
depending only on the mollifier, the regularization scale and k. -/
theorem regularisedSchwartzTensorBilinear_bessel_even_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g f : 𝓢(L2Vec3, ComplexVec3),
        ‖((regularisedSchwartzTensorBilinear ρ ε hε g f).memSobolev
            (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace‖ ≤
          C * ‖g.toLp 2‖ *
            ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖ := by
  obtain ⟨A, hA, hIter⟩ :=
    regularisedSchwartzBesselStep_iterate_iteratedFDeriv_norm_le
      (F := ComplexTensor3) ((2 * Real.pi) ^ 2)⁻¹ k
  have hK : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3),
        ‖regularisedSchwartzMollifyDerivative ρ ε hε i ψ x‖ ≤
          K * ‖ψ.toLp 2‖ :=
    fun i => regularisedSchwartzMollify_iteratedFDeriv_uniformBound ρ ε hε i
  choose K hK0 hKb using hK
  obtain ⟨B, hB, hBb⟩ := regularisedSchwartz_iteratedFDeriv_sum_eLpNorm_le_bessel k
  let c : ℕ → ℝ := fun m =>
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * K i
  have hc : ∀ m, 0 ≤ c m := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hK0 i)
  let L : ℝ := A * ∑ m ∈ Finset.range (2 * k + 1), c m
  have hL : 0 ≤ L := mul_nonneg hA (Finset.sum_nonneg fun m _ => hc m)
  refine ⟨L * B, mul_nonneg hL hB, ?_⟩
  intro g f
  let Φ : ComplexVec3 →L[ℝ] ComplexVec3 →L[ℝ] ComplexTensor3 :=
    regularisedComplexTensorOuterCLM.bilinearRestrictScalars ℝ
  have hΦ : ‖Φ‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_bilinearRestrictScalars]
    apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
    intro v u
    rw [one_mul]
    exact (regularisedComplexTensorOuter_norm v u).le
  let G : 𝓢(L2Vec3, ComplexVec3) := regularisedSchwartzMollify ρ ε hε g
  let T : 𝓢(L2Vec3, ComplexTensor3) := regularisedSchwartzTensorBilinear ρ ε hε g f
  have hTfun : (T : L2Vec3 → ComplexTensor3) = fun y => Φ (G y) (f y) := by
    funext y
    rfl
  let V : ℝ := ‖g.toLp 2‖
  have hV : 0 ≤ V := norm_nonneg _
  let S : L2Vec3 → ℝ := fun x => ∑ p ∈ Finset.range (2 * k + 1),
    ‖iteratedFDeriv ℝ p f x‖
  have hDer (m : ℕ) (hm : m ≤ 2 * k) (x : L2Vec3) :
      ‖iteratedFDeriv ℝ m T x‖ ≤ c m * V * S x := by
    have hLeib := Φ.norm_iteratedFDeriv_le_of_bilinear_of_le_one
      (G.smooth ⊤) (f.smooth ⊤) x (n := m) (by exact_mod_cast le_top) hΦ
    rw [hTfun]
    refine hLeib.trans ?_
    have hterm (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i G x‖ *
            ‖iteratedFDeriv ℝ (m - i) f x‖ ≤
          (m.choose i : ℝ) * K i * V * S x := by
      have hG : ‖iteratedFDeriv ℝ i G x‖ ≤ K i * V := by
        have h := hKb i g x
        rw [regularisedSchwartzMollifyDerivative] at h
        exact h
      have hF : ‖iteratedFDeriv ℝ (m - i) f x‖ ≤ S x := by
        have hmem : m - i ∈ Finset.range (2 * k + 1) := by
          rw [Finset.mem_range]
          omega
        exact Finset.single_le_sum (f := fun p => ‖iteratedFDeriv ℝ p f x‖)
          (fun p _ => norm_nonneg _) hmem
      calc
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i G x‖ *
            ‖iteratedFDeriv ℝ (m - i) f x‖ ≤
            (m.choose i : ℝ) * (K i * V) * S x := by
          have h0 : 0 ≤ (m.choose i : ℝ) * (K i * V) :=
            mul_nonneg (by positivity) (mul_nonneg (hK0 i) hV)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hG (by positivity)) hF
            (norm_nonneg _) h0
        _ = (m.choose i : ℝ) * K i * V * S x := by ring
    calc
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i G x‖ * ‖iteratedFDeriv ℝ (m - i) f x‖ ≤
          ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * K i * V * S x :=
        Finset.sum_le_sum hterm
      _ = c m * V * S x := by
        change _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * K i) * V * S x
        rw [Finset.sum_mul, Finset.sum_mul]
  let P := regularisedSchwartzBesselStep (F := ComplexTensor3) ((2 * Real.pi) ^ 2)⁻¹
  have hPoint (x : L2Vec3) : ‖(P^[k] T) x‖ ≤ ((L * V) • S) x := by
    have h := hIter T 0 x
    rw [norm_iteratedFDeriv_zero] at h
    have hzero : ∑ m ∈ Finset.range (2 * k + 1), ‖iteratedFDeriv ℝ (0 + m) T x‖ =
        ∑ m ∈ Finset.range (2 * k + 1), ‖iteratedFDeriv ℝ m T x‖ :=
      Finset.sum_congr rfl fun m _ => by rw [Nat.zero_add]
    rw [hzero] at h
    refine h.trans ?_
    have hsum : ∑ m ∈ Finset.range (2 * k + 1), ‖iteratedFDeriv ℝ m T x‖ ≤
        ∑ m ∈ Finset.range (2 * k + 1), c m * V * S x := by
      apply Finset.sum_le_sum
      intro m hm
      exact hDer m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) x
    calc
      A * ∑ m ∈ Finset.range (2 * k + 1), ‖iteratedFDeriv ℝ m T x‖ ≤
          A * ∑ m ∈ Finset.range (2 * k + 1), c m * V * S x := by
        gcongr
      _ = ((L * V) • S) x := by
        simp only [L, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
  have hMeas : AEStronglyMeasurable (P^[k] T : L2Vec3 → ComplexTensor3) volume :=
    (P^[k] T).continuous.aestronglyMeasurable
  have hS := hBb f
  have hEl : eLpNorm (P^[k] T : L2Vec3 → ComplexTensor3) 2 volume ≤
      ENNReal.ofReal ((L * V) *
        (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖)) := by
    calc
      eLpNorm (P^[k] T : L2Vec3 → ComplexTensor3) 2 volume ≤
          eLpNorm ((L * V) • S) 2 volume :=
        eLpNorm_mono_real hMeas hPoint
      _ ≤ ‖L * V‖ₑ * eLpNorm S 2 volume := eLpNorm_const_smul_le
      _ ≤ ‖L * V‖ₑ * ENNReal.ofReal
          (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖) := by
        gcongr
      _ = ENNReal.ofReal ((L * V) *
          (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖)) := by
        rw [Real.enorm_eq_ofReal (mul_nonneg hL hV),
          ENNReal.ofReal_mul (mul_nonneg hL hV)]
  have hNorm := regularisedTensor_schwartz_bessel_even_norm_eq k T
  change ‖(T.memSobolev (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace‖ ≤
    L * B * V * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖
  rw [hNorm, SchwartzMap.norm_toLp]
  have hReal := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg hL hV) (mul_nonneg hB (norm_nonneg _))) hEl
  calc
    (eLpNorm (P^[k] T : L2Vec3 → ComplexTensor3) 2 volume).toReal ≤
        (L * V) * (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖) :=
      hReal
    _ = L * B * V * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖ := by
      ring

end CKN.Leray

end
