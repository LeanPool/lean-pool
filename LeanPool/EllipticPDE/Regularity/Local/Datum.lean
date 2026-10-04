/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Local.InteriorH2


/-!
# Higher-order datum of the cutoff reduction

The cutoff reduction of `Local/Reduction.lean` hands `η U` an equation whose datum pairs `f`,
`U₀` and the gradient coordinates of `U` against bounded weights supported in `tsupport η`. The
higher-order induction of Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2
applies the `H₀¹` theorem at order `k` to `η U`, and so asks the datum for `k` weak derivatives
with a bound.

Every term of the datum is a cutoff, a `W^{k,∞}` coefficient and a coordinate of `U`, which is
the shape `exists_datum_of_pieces` assembles. The coordinates of `U` are only asked for `k`
weak derivatives on the support of the cutoff, which is what the induction has available one
order down; the datum `f` is asked for them on `Ω`. The derivative of the principal coefficient
is the first member of its `W^{k+1,∞}` family, through `IsWkInftyCoeff.coeffWeakGrad`, so the
pairing reads off `reduction_testFn` with no classical derivative anywhere.

## Main declarations

* `setIntegral_cutoff_restrict_eq`: a piece on the support of the cutoff as an integral on `Ω`.
* `exists_reductionDatum`: the datum, its family, its bound and its pairing.
* `exists_collarFamily_of_weakDerivOn`: `exists_collarFamily` with a weak derivative on the
  outer set in place of one on the whole space.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Extension

variable {d : ℕ}

/-- **Piece on the support of the cutoff as an integral on `Ω`.** For `χ` supported in
`N`, pairing the restriction of `g` to `N` against `χ c v` on `N` is pairing `g` against
`c χ v` on `Ω`. -/
theorem setIntegral_cutoff_restrict_eq {Ω N : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : tsupport χ ⊆ N)
    (c v : EuclideanSpace ℝ (Fin d) → ℝ) (g : L2D Ω) :
    ∫ x in N, χ x * (c x * (restrictL2 (Ω := N) (extendL2 hΩm g) x : ℝ)) * v x
      = ∫ x in Ω, c x * (g x : ℝ) * (χ x * v x) := by
  have hχ0 : ∀ x, x ∉ N → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hχ hc))
  have e1 : ∫ x in N, χ x * (c x * (restrictL2 (Ω := N) (extendL2 hΩm g) x : ℝ)) * v x
      = ∫ x in N, χ x * (c x * (extendL2 hΩm g x : ℝ)) * v x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_restrictL2 (Ω := N) (extendL2 hΩm g)] with x hx
    rw [hx]
  have e2 : ∫ x in N, χ x * (c x * (extendL2 hΩm g x : ℝ)) * v x
      = ∫ x, χ x * (c x * (extendL2 hΩm g x : ℝ)) * v x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hχ0 x hx]; ring
  have e3 : ∫ x in Ω, c x * (g x : ℝ) * (χ x * v x)
      = ∫ x, c x * (extendL2 hΩm g x : ℝ) * (χ x * v x) :=
    (integral_extendL2_mul_mul hΩm g c (fun x => χ x * v x)).symm
  rw [e1, e2, e3]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

section Datum

variable {n : ℕ}

/-- **Datum of the cutoff reduction at order `k`.** For a cutoff `η` supported in `N ⊆ Ω`, with
`W^{k+1,∞}` principal and `W^{k,∞}` transport coefficients, there is a constant `K` such that
every `U` whose coordinates have `k` weak derivatives on `N`, and every datum `f` with `k` weak
derivatives on `Ω`, all bounded by `B`, give an `L²(Ω)` class with `k` weak derivatives bounded
by `K B` pairing against a test function as the datum of `reduction_testFn`. -/
theorem exists_reductionDatum (Op : FullEllipticOp (n + 1))
    {Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩm : MeasurableSet Ω) (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1)) (hbc : IsWkInftyLower Op k)
    {η : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hη : IsTestFn N η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : H1amb Ω) (f : L2D Ω)
      (HU : ∀ j : Fin (n + 2),
        HasIteratedWeakDerivOn N k (restrictL2 (Ω := N) (extendL2 hΩm (U j))))
      (Hf : HasIteratedWeakDerivOn Ω k f) (B : ℝ),
      (∀ j, IteratedL2Bound (HU j) B) → IteratedL2Bound Hf B →
      ∃ (F : L2D Ω) (HF : HasIteratedWeakDerivOn Ω k F),
        IteratedL2Bound HF (K * B) ∧
        ∀ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
          HasCompactSupport v →
          (∫ x in Ω, (F x : ℝ) * v x)
            = (∫ x in Ω, (f x : ℝ) * (η x * v x))
              - (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                  ∫ x in Ω, Op.a x i j * (U i.succ x : ℝ) * (partialD j η x * v x))
              - (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∫ x in Ω,
                  hA.coeffWeakGrad.da j i j x * (U 0 x : ℝ) * (partialD i η x * v x))
              - (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                  ∫ x in Ω, Op.a x i j * (U j.succ x : ℝ) * (partialD i η x * v x))
              - (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∫ x in Ω,
                  Op.a x i j * (U 0 x : ℝ) * (partialD j (partialD i η) x * v x))
              + (∑ i : Fin (n + 1),
                  ∫ x in Ω, Op.b x i * (U 0 x : ℝ) * (partialD i η x * v x)) := by
  classical
  have hηΩ : IsTestFn Ω η := ⟨hη.1, hη.2.1, hη.2.2.trans hNΩ⟩
  have haE : ∀ i j : Fin (n + 1), IsWkInfty (fun x => Op.a x i j) k :=
    fun i j => (hA.entry i j).mono (by omega)
  have haD : ∀ i j m : Fin (n + 1), IsWkInfty ((hA.entry i j).D [m]) k :=
    fun i j m => (hA.entry i j).deriv m
  have hbE : ∀ i : Fin (n + 1), IsWkInfty (fun x => Op.b x i) k := fun i => hbc.bReg i
  have hηD : ∀ i : Fin (n + 1), IsTestFn N (partialD i η) := fun i => isTestFn_partialD hη i
  have hηDD : ∀ i j : Fin (n + 1), IsTestFn N (partialD j (partialD i η)) :=
    fun i j => isTestFn_partialD (hηD i) j
  obtain ⟨K1, hK1, hP1⟩ := exists_datum_piece hΩm subset_rfl k hηΩ (IsWkInfty.const 1 k)
  obtain ⟨K2, hK2, hP2⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.2 η) (fun t => hηD t.2)
    (a := fun t => fun x => Op.a x t.1 t.2) (fun t => haE t.1 t.2)
  obtain ⟨K3, hK3, hP3⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.1 η) (fun t => hηD t.1)
    (a := fun t => hA.D [t.2] t.1 t.2) (fun t => haD t.1 t.2 t.2)
  obtain ⟨K4, hK4, hP4⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.1 η) (fun t => hηD t.1)
    (a := fun t => fun x => Op.a x t.1 t.2) (fun t => haE t.1 t.2)
  obtain ⟨K5, hK5, hP5⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.2 (partialD t.1 η)) (fun t => hηDD t.1 t.2)
    (a := fun t => fun x => Op.a x t.1 t.2) (fun t => haE t.1 t.2)
  obtain ⟨K6, hK6, hP6⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Fin (n + 1))
    (χ := fun i => partialD i η) hηD (a := fun i => fun x => Op.b x i) hbE
  refine ⟨K1 + K2 + K3 + K4 + K5 + K6, by linarith, ?_⟩
  intro U f HU Hf B hHU hHf
  obtain ⟨F1, HF1, hB1, hp1⟩ := hP1 Hf hHf
  obtain ⟨F2, HF2, hB2, hp2⟩ := hP2 (fun t => restrictL2 (Ω := N) (extendL2 hΩm (U t.1.succ)))
    (fun t => HU t.1.succ) (fun t => hHU t.1.succ)
  obtain ⟨F3, HF3, hB3, hp3⟩ := hP3 (fun _ => restrictL2 (Ω := N) (extendL2 hΩm (U 0)))
    (fun _ => HU 0) (fun _ => hHU 0)
  obtain ⟨F4, HF4, hB4, hp4⟩ := hP4 (fun t => restrictL2 (Ω := N) (extendL2 hΩm (U t.2.succ)))
    (fun t => HU t.2.succ) (fun t => hHU t.2.succ)
  obtain ⟨F5, HF5, hB5, hp5⟩ := hP5 (fun _ => restrictL2 (Ω := N) (extendL2 hΩm (U 0)))
    (fun _ => HU 0) (fun _ => hHU 0)
  obtain ⟨F6, HF6, hB6, hp6⟩ := hP6 (fun _ => restrictL2 (Ω := N) (extendL2 hΩm (U 0)))
    (fun _ => HU 0) (fun _ => hHU 0)
  refine ⟨F1 - F2 - F3 - F4 - F5 + F6, ((((HF1.sub HF2).sub HF3).sub HF4).sub HF5).add HF6,
    ?_, fun v hvc hvcs => ?_⟩
  · have hB := ((((hB1.sub hB2).sub hB3).sub hB4).sub hB5).add hB6
    refine hB.mono_const (le_of_eq ?_)
    ring
  · rw [setIntegral_add_mul_testFn _ _ hvc hvcs, setIntegral_sub_mul_testFn _ _ hvc hvcs,
      setIntegral_sub_mul_testFn _ _ hvc hvcs, setIntegral_sub_mul_testFn _ _ hvc hvcs,
      setIntegral_sub_mul_testFn _ _ hvc hvcs,
      hp1 v, hp2 v hvc hvcs, hp3 v hvc hvcs, hp4 v hvc hvcs, hp5 v hvc hvcs, hp6 v hvc hvcs]
    simp only [Fintype.sum_prod_type]
    have hηt : ∀ i : Fin (n + 1), tsupport (partialD i η) ⊆ N := fun i => (hηD i).2.2
    have hηtt : ∀ i j : Fin (n + 1), tsupport (partialD j (partialD i η)) ⊆ N :=
      fun i j => (hηDD i j).2.2
    simp only [setIntegral_cutoff_restrict_eq hΩm (hηt _),
      setIntegral_cutoff_restrict_eq hΩm (hηtt _ _)]
    have h1 : ∫ x in Ω, η x * ((1 : ℝ) * (f x : ℝ)) * v x = ∫ x in Ω, (f x : ℝ) * (η x * v x) :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [h1]
    rfl

end Datum

/-- **Inductive family moved to the collar from a weak derivative on the outer set.** The
statement of `exists_collarFamily`, with the whole-space weak derivative of `g` replaced by one
on `W`. A solution with no boundary condition has its gradient as a weak derivative on `Ω` and
on every subset, and never on the whole space after extension by zero. -/
theorem exists_collarFamily_of_weakDerivOn {Ω W N : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hNm : MeasurableSet N) (hNW : N ⊆ W)
    {θ : EuclideanSpace ℝ (Fin d) → ℝ} (hθW : IsTestFn W θ) (hθN : Set.EqOn θ 1 N)
    {g : L2D Ω} {Dg : Fin d → L2D Ω}
    (hDgW : ∀ i, HasWeakDerivOn W i (restrictL2 (Ω := W) (extendL2 hΩm g))
      (restrictL2 (Ω := W) (extendL2 hΩm (Dg i)))) {m : ℕ} {C : ℝ}
    (HuW : HasIteratedWeakDerivOn W (m + 1) (restrictL2 (Ω := W) (extendL2 hΩm g)))
    (hHuW : IteratedL2Bound HuW C) :
    ∃ HuN : HasIteratedWeakDerivOn N (m + 1) (restrictL2 (Ω := N) (extendL2 hΩm g)),
      IteratedL2Bound HuN C ∧
      ∀ i : Fin d, HuN.D [i] = restrictL2 (Ω := N) (extendL2 hΩm (Dg i)) := by
  refine ⟨(HuW.restrict hWm hNm hNW).congr (restrictL2_extendL2_trans hΩm hWm hNm hNW g),
    IteratedL2Bound.congr (h := restrictL2_extendL2_trans hΩm hWm hNm hNW g)
      (IteratedL2Bound.restrict (hWm := hWm) (hVm := hNm) (hVW := hNW) hHuW), fun i => ?_⟩
  have h1 : HasWeakDerivOn W i (restrictL2 (Ω := W) (extendL2 hΩm g)) (HuW.D [i]) := by
    have h := HuW.D_step i [] (Nat.succ_pos m)
    rwa [HuW.D_nil] at h
  change restrictL2 (Ω := N) (extendL2 hWm (HuW.D [i])) = _
  rw [restrictL2_extendL2_congr_of_weakDerivOn hWm hNm hNW hθW hθN h1 (hDgW i),
    restrictL2_extendL2_trans hΩm hWm hNm hNW]

end EllipticPdes.Regularity
