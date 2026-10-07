/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselDerivativeL2Map
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexFiniteDimensional

/-!
# Physical derivatives of Schwartz fields through the even Bessel order

Every Fréchet derivative of order at most 2k of a complex Schwartz
velocity has L² norm bounded by a fixed multiple of the complete H²ᵏ
norm of its canonical Sobolev lift.
-/

public section

open MeasureTheory
open scoped ENNReal SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv

/-- The ordered distributional derivative along the reversed list of a
tuple of directions is the iterated directional derivative along the
tuple. -/
theorem regularisedDistribution_foldl_ofFn_rev_eq_iteratedLineDerivOp
    {n : ℕ} (m : Fin n → L2Vec3) (D : 𝓢'(L2Vec3, ComplexVec3)) :
    (List.ofFn (fun a => m (Fin.rev a))).foldl (fun F v => ∂_{v} F) D =
      ∂^{m} D := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat,
        iteratedLineDerivOp_succ_left, Fin.rev_last]
      have hfun : (fun i : Fin n => m (Fin.rev (Fin.castSucc i))) =
          (fun i : Fin n => Fin.tail m (Fin.rev i)) := by
        funext i
        rw [Fin.rev_castSucc]
        rfl
      rw [hfun, ih]

/-- Iterated directional derivatives commute with the embedding of
Schwartz fields into tempered distributions. -/
theorem regularisedSchwartz_iteratedLineDerivOp_toTemperedDistribution
    {n : ℕ} (m : Fin n → L2Vec3) (f : 𝓢(L2Vec3, ComplexVec3)) :
    ∂^{m} (f : 𝓢'(L2Vec3, ComplexVec3)) =
      ((∂^{m} f : 𝓢(L2Vec3, ComplexVec3)) : 𝓢'(L2Vec3, ComplexVec3)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, ih,
        TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]

/-- Each iterated directional derivative of order at most 2k of a
complex Schwartz velocity is bounded in L² by the complete H²ᵏ norm of
its canonical Sobolev lift. -/
theorem regularisedSchwartz_iteratedLineDerivOp_toLp_norm_le_bessel
    (k : ℕ) {p : ℕ} (hp : p ≤ 2 * k) (m : Fin p → L2Vec3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(L2Vec3, ComplexVec3),
      ‖(∂^{m} f : 𝓢(L2Vec3, ComplexVec3)).toLp 2‖ ≤
        C * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖ := by
  let α : List L2Vec3 := List.ofFn (fun a => m (Fin.rev a))
  have hα : α.length ≤ 2 * k := by
    simpa only [α, List.length_ofFn] using hp
  obtain ⟨C, hC, hBound⟩ := regularisedBesselEvenOrderedDerivativeL2_norm_le k α hα
  refine ⟨C, hC, ?_⟩
  intro f
  have hEq : regularisedBesselEvenOrderedDerivativeL2 k α hα
      (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f) =
        (∂^{m} f : 𝓢(L2Vec3, ComplexVec3)).toLp 2 := by
    apply (LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
        (F := ComplexVec3) (μ := volume) (p := 2)))
    have hD := regularisedBesselEvenOrderedDerivativeL2_toDistr k α hα
      (regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f)
    rw [regularisedOrderedDistributionDerivativeCLM_apply,
      regularisedBesselOfSchwartz_toDistr,
      regularisedDistribution_foldl_ofFn_rev_eq_iteratedLineDerivOp,
      regularisedSchwartz_iteratedLineDerivOp_toTemperedDistribution,
      ← Lp.toTemperedDistribution_toLp_eq (p := 2) (μ := volume)] at hD
    exact hD
  rw [← hEq]
  exact hBound _

/-- The L² norm of the p-th Fréchet derivative of a complex Schwartz
velocity is bounded by the complete H²ᵏ norm when p ≤ 2k. -/
theorem regularisedSchwartz_iteratedFDeriv_eLpNorm_le_bessel
    (k : ℕ) {p : ℕ} (hp : p ≤ 2 * k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : 𝓢(L2Vec3, ComplexVec3),
      eLpNorm (fun x : L2Vec3 => ‖iteratedFDeriv ℝ p f x‖) 2 volume ≤
        ENNReal.ofReal
          (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖) := by
  have hw : ∀ w : Fin p → Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(L2Vec3, ComplexVec3),
        ‖(∂^{regularisedSchwartzCoordinateTuple w} f :
          𝓢(L2Vec3, ComplexVec3)).toLp 2‖ ≤
          C * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖ :=
    fun w => regularisedSchwartz_iteratedLineDerivOp_toLp_norm_le_bessel k hp
      (regularisedSchwartzCoordinateTuple w)
  choose C hC hCb using hw
  let N : ℝ := (Fintype.card (Fin p → Fin 3) : ℝ)
  have hN : 0 ≤ N := by positivity
  refine ⟨N * ∑ w, C w, mul_nonneg hN (Finset.sum_nonneg fun w _ => hC w), ?_⟩
  intro f
  let V : ℝ := ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖
  have hV : 0 ≤ V := norm_nonneg _
  let g : (Fin p → Fin 3) → L2Vec3 → ℝ := fun w x =>
    ‖(∂^{regularisedSchwartzCoordinateTuple w} f : 𝓢(L2Vec3, ComplexVec3)) x‖
  have hPoint (x : L2Vec3) :
      ‖‖iteratedFDeriv ℝ p f x‖‖ ≤ (N • ∑ w, g w) x := by
    rw [norm_norm]
    have hcoord := regularisedComplexMultilinear_norm_le_coordinateBound
      (iteratedFDeriv ℝ p f x) (∑ w, g w x)
      (Finset.sum_nonneg fun w _ => norm_nonneg _) (by
        intro w
        have happ : iteratedFDeriv ℝ p f x
            (fun a => regularisedSchwartzCoordinateDirection (w a)) =
            (∂^{regularisedSchwartzCoordinateTuple w} f :
              𝓢(L2Vec3, ComplexVec3)) x :=
          SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
        rw [happ]
        exact Finset.single_le_sum (f := fun w => g w x)
          (fun w _ => norm_nonneg _) (Finset.mem_univ w))
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using hcoord
  have hMeas : AEStronglyMeasurable
      (fun x : L2Vec3 => ‖iteratedFDeriv ℝ p f x‖) volume :=
    ((f.smooth p).continuous_iteratedFDeriv le_rfl).norm.aestronglyMeasurable
  have hEach (w : Fin p → Fin 3) :
      eLpNorm (g w) 2 volume ≤ ENNReal.ofReal (C w * V) := by
    let h : 𝓢(L2Vec3, ComplexVec3) := ∂^{regularisedSchwartzCoordinateTuple w} f
    have hnorm : eLpNorm (g w) 2 volume = eLpNorm (h : L2Vec3 → ComplexVec3) 2 volume :=
      eLpNorm_norm _ h.continuous.aestronglyMeasurable
    have hfin : eLpNorm (h : L2Vec3 → ComplexVec3) 2 volume ≠ ⊤ :=
      (h.memLp 2 volume).eLpNorm_ne_top
    have htoLp : ‖h.toLp 2‖ = (eLpNorm (h : L2Vec3 → ComplexVec3) 2 volume).toReal :=
      SchwartzMap.norm_toLp
    rw [hnorm, ← ENNReal.ofReal_toReal hfin, ← htoLp]
    exact ENNReal.ofReal_le_ofReal (hCb w f)
  calc
    eLpNorm (fun x : L2Vec3 => ‖iteratedFDeriv ℝ p f x‖) 2 volume ≤
        eLpNorm (N • ∑ w, g w) 2 volume :=
      eLpNorm_mono_real hMeas hPoint
    _ ≤ ‖N‖ₑ * eLpNorm (∑ w, g w) 2 volume := eLpNorm_const_smul_le
    _ ≤ ‖N‖ₑ * ∑ w, eLpNorm (g w) 2 volume := by
      gcongr
      exact eLpNorm_sum_le (by norm_num)
    _ ≤ ‖N‖ₑ * ∑ w, ENNReal.ofReal (C w * V) := by
      gcongr with w
      exact hEach w
    _ = ENNReal.ofReal (N * ∑ w, C w * V) := by
      rw [Real.enorm_eq_ofReal hN, ENNReal.ofReal_mul hN,
        ENNReal.ofReal_sum_of_nonneg (fun w _ => mul_nonneg (hC w) hV)]
    _ = ENNReal.ofReal ((N * ∑ w, C w) * V) := by
      rw [mul_assoc, Finset.sum_mul]

/-- The sum of the pointwise norms of all Fréchet derivatives through
order 2k of a complex Schwartz velocity is bounded in L² by the
complete H²ᵏ norm of its canonical Sobolev lift. -/
theorem regularisedSchwartz_iteratedFDeriv_sum_eLpNorm_le_bessel (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : 𝓢(L2Vec3, ComplexVec3),
      eLpNorm (fun x : L2Vec3 => ∑ p ∈ Finset.range (2 * k + 1),
          ‖iteratedFDeriv ℝ p f x‖) 2 volume ≤
        ENNReal.ofReal
          (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖) := by
  have hp : ∀ p ∈ Finset.range (2 * k + 1), ∃ B : ℝ, 0 ≤ B ∧
      ∀ f : 𝓢(L2Vec3, ComplexVec3),
        eLpNorm (fun x : L2Vec3 => ‖iteratedFDeriv ℝ p f x‖) 2 volume ≤
          ENNReal.ofReal
            (B * ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖) := by
    intro p hp
    exact regularisedSchwartz_iteratedFDeriv_eLpNorm_le_bessel k
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))
  choose! B hB hBb using hp
  refine ⟨∑ p ∈ Finset.range (2 * k + 1), B p,
    Finset.sum_nonneg fun p hp => hB p hp, ?_⟩
  intro f
  let V : ℝ := ‖regularisedBesselOfSchwartz ((2 * k : ℕ) : ℝ) f‖
  have hV : 0 ≤ V := norm_nonneg _
  let g : ℕ → L2Vec3 → ℝ := fun p x => ‖iteratedFDeriv ℝ p f x‖
  have hfun : (fun x : L2Vec3 => ∑ p ∈ Finset.range (2 * k + 1),
      ‖iteratedFDeriv ℝ p f x‖) = ∑ p ∈ Finset.range (2 * k + 1), g p := by
    funext x
    simp only [g, Finset.sum_apply]
  rw [hfun]
  calc
    eLpNorm (∑ p ∈ Finset.range (2 * k + 1), g p) 2 volume ≤
        ∑ p ∈ Finset.range (2 * k + 1), eLpNorm (g p) 2 volume :=
      eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ p ∈ Finset.range (2 * k + 1), ENNReal.ofReal (B p * V) :=
      Finset.sum_le_sum fun p hp => hBb p hp f
    _ = ENNReal.ofReal ((∑ p ∈ Finset.range (2 * k + 1), B p) * V) := by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun p hp => mul_nonneg (hB p hp) hV), Finset.sum_mul]

end CKN.Leray

end
