/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldPipeline
public import LeanPool.HyperellipticCurves.Log.Fold.FoldWitness

/-!
# The class computation of the fold pipeline

The field-level class computation of the point-by-point fold pipeline. Each fold step multiplies
the represented ideal class by the class of the added point (`ChabautyColeman.mk0_foldPipeStep`),
so the pipeline output represents the sum of the start's class and all point classes
(`ChabautyColeman.mk0_foldPipe`). At the mirrored two-phase point block — the shape of the centre
configuration and of the collapsed fold-`F_τ` configurations — the point classes cancel pair by
pair, no `τ`-class bookkeeping needed (`ChabautyColeman.prod_mk0_foldXs_foldYs`).

## Main statements

* `ChabautyColeman.fold_pipeline_eq_self`: at the mirrored point block the fold returns its start —
  the pointwise content of the unit laws and of the centre value of `F_τ`, by the class computation
  and uniqueness of reduced Mumford representatives.
* `ChabautyColeman.fold_pipeline_eq_of_mk0_eq`: two folds whose inputs represent the same total
  class have equal outputs — the engine of pack-independence and of the class-group identities
  behind the group-law axioms of `F_τ`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

open nonZeroDivisors

section ClassEngine

variable {K : Type*} [Field K] {f : K[X]} [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)] {g : ℕ}

/-- **One fold step multiplies the class by the added point's class**: the composition
computes the product and the `(-1)`-reduction preserves it. -/
theorem mk0_foldPipeStep {p : K[X] × K[X]} {x y : K} {c : FoldTriple K}
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1) (hp : IsFoldState g f p.1 p.2)
    (hbez : c.s₁ * p.1 + c.s₂ * (X - C x) + c.s₃ * (p.2 + C y) = 1)
    (hcv : y ^ 2 = f.eval x) :
    ClassGroup.mk0 ⟨mumfordIdeal f (foldPipeStep f p x y c).1 (foldPipeStep f p x y c).2,
        mumfordIdeal_mem_nonZeroDivisors f
          (isFoldState_foldPipeStep hf hfdeg hp hbez hcv).monicU.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f p.1 p.2,
            mumfordIdeal_mem_nonZeroDivisors f hp.monicU.ne_zero p.2⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f (X - C x) (C y),
            mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x).ne_zero (C y)⟩ := by
  have hqm : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1.Monic :=
    cantorCompose_monic f hp.monicU (monic_X_sub_C x)
  have hqdvd := cantorCompose_dvd f hbez hp.dvd_sq (X_sub_C_dvd_of_sq_eq hcv)
  obtain ⟨hc, -⟩ := foldPipeStep_cofactor_lc hf hfdeg hp hbez hcv
  exact (mk0_cantorReduce f hqm hqdvd hc).symm.trans
    (mk0_cantorCompose f hp.monicU (monic_X_sub_C x) hbez hp.dvd_sq
      (X_sub_C_dvd_of_sq_eq hcv))

variable {xs ys : ℕ → K} {d : ℕ → FoldTriple K} {U₀ V₀ : K[X]}

/-- **The class of the fold pipeline**: the pipeline output represents the sum of the
start's class and the classes of all added points. -/
theorem mk0_foldPipe (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (h₀ : IsFoldState g f U₀ V₀) {m : ℕ}
    (hbez : ∀ j < m, (d j).s₁ * (foldPipe f xs ys d U₀ V₀ j).1
      + (d j).s₂ * (X - C (xs j))
      + (d j).s₃ * ((foldPipe f xs ys d U₀ V₀ j).2 + C (ys j)) = 1)
    (hcv : ∀ j < m, ys j ^ 2 = f.eval (xs j))
    (hm : (foldPipe f xs ys d U₀ V₀ m).1.Monic) :
    ClassGroup.mk0 ⟨mumfordIdeal f (foldPipe f xs ys d U₀ V₀ m).1
        (foldPipe f xs ys d U₀ V₀ m).2,
        mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f U₀ V₀,
            mumfordIdeal_mem_nonZeroDivisors f h₀.monicU.ne_zero V₀⟩
        * ∏ j ∈ Finset.range m,
            ClassGroup.mk0 ⟨mumfordIdeal f (X - C (xs j)) (C (ys j)),
              mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C (xs j)).ne_zero
                (C (ys j))⟩ := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.prod_empty, mul_one]
    rfl
  | succ m ih =>
    have hprev := isFoldState_foldPipe (m := m) hf hfdeg h₀
      (fun j hj ↦ hbez j (by lia)) fun j hj ↦ hcv j (by lia)
    rw [Finset.prod_range_succ, ← mul_assoc,
      ← ih (fun j hj ↦ hbez j (by lia)) (fun j hj ↦ hcv j (by lia)) hprev.monicU]
    exact mk0_foldPipeStep hf hfdeg hprev (hbez m (by lia)) (hcv m (by lia))

/-- The class of a point datum depends only on the coordinate values. -/
theorem mk0_point_congr {x x' y y' : K} (hx : x = x') (hy : y = y') :
    ClassGroup.mk0 ⟨mumfordIdeal f (X - C x) (C y),
        mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x).ne_zero (C y)⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (X - C x') (C y'),
          mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x').ne_zero (C y')⟩ := by
  subst hx hy
  rfl

/-- A point and its involution cancel in the class group. -/
private theorem mk0_point_mul_neg {x y : K} (hcv : y ^ 2 = f.eval x) :
    ClassGroup.mk0 ⟨mumfordIdeal f (X - C x) (C y),
        mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x).ne_zero (C y)⟩
      * ClassGroup.mk0 ⟨mumfordIdeal f (X - C x) (C (-y)),
          mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x).ne_zero (C (-y))⟩
      = 1 := by
  have h : ClassGroup.mk0 ⟨mumfordIdeal f (X - C x) (C (-y)),
        mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x).ne_zero (C (-y))⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (X - C x) (-C y),
          mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C x).ne_zero (-C y)⟩ :=
    congrArg ClassGroup.mk0 (Subtype.ext (congrArg (mumfordIdeal f (X - C x)) (map_neg C y)))
  rw [h]
  exact mk0_mumfordIdeal_mul_neg f (monic_X_sub_C x) (X_sub_C_dvd_of_sq_eq hcv)

/-- **The mirrored point block cancels**: at the two-phase shape that revisits its points
in reverse order with negated square roots, the product of all `2g` point classes is
trivial — the second phase inverts the first pair by pair. -/
theorem prod_mk0_foldXs_foldYs {α β : Fin g → K} (hcv : ∀ i, β i ^ 2 = f.eval (α i)) :
    ∏ j ∈ Finset.range (2 * g),
        ClassGroup.mk0 ⟨mumfordIdeal f (X - C (foldXs α j)) (C (foldYs β j)),
          mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C (foldXs α j)).ne_zero
            (C (foldYs β j))⟩ = 1 := by
  rw [two_mul, Finset.prod_range_add, ← Finset.prod_range_reflect (fun j ↦ ClassGroup.mk0
      ⟨mumfordIdeal f (X - C (foldXs α (g + j))) (C (foldYs β (g + j))),
        mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C (foldXs α (g + j))).ne_zero
          (C (foldYs β (g + j)))⟩) g,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j hj ↦ ?_
  have hjg := Finset.mem_range.mp hj
  have hx1 : foldXs α j = α ⟨j, hjg⟩ := dite_eq_left hjg
  have hy1 : foldYs β j = β ⟨j, hjg⟩ := dite_eq_left hjg
  have hx2 : foldXs α (g + (g - 1 - j)) = α ⟨j, hjg⟩ := by
    rw [foldXs_add α (by lia)]
    exact congrArg α (Fin.ext (by simp only [Fin.val_rev]; lia))
  have hy2 : foldYs β (g + (g - 1 - j)) = -β ⟨j, hjg⟩ := by
    rw [foldYs_add β (by lia)]
    exact congrArg (- β ·) (Fin.ext (by simp only [Fin.val_rev]; lia))
  rw [mk0_point_congr hx1 hy1, mk0_point_congr hx2 hy2]
  exact mk0_point_mul_neg (hcv ⟨j, hjg⟩)

/-- **The `K`-level fold pipeline at the mirrored point block computes `c + τ - τ = c`**: with
valid Bézout triples along the two-phase shape, the `2g`-step fold returns its start. The pointwise
content of the unit laws and of the centre value of `F_τ`. -/
theorem fold_pipeline_eq_self {α β : Fin g → K} (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (h₀ : IsFoldState g f U₀ V₀)
    (hcv : ∀ i, β i ^ 2 = f.eval (α i))
    (hbez : ∀ j < 2 * g,
      (d j).s₁ * (foldPipe f (foldXs α) (foldYs β) d U₀ V₀ j).1
        + (d j).s₂ * (X - C (foldXs α j))
        + (d j).s₃ * ((foldPipe f (foldXs α) (foldYs β) d U₀ V₀ j).2
            + C (foldYs β j)) = 1) :
    foldPipe f (foldXs α) (foldYs β) d U₀ V₀ (2 * g) = (U₀, V₀) := by
  have hcv' : ∀ j < 2 * g, foldYs β j ^ 2 = f.eval (foldXs α j) :=
    fun j hj ↦ foldYs_sq hcv hj
  have hst := isFoldState_foldPipe (m := 2 * g) hf hfdeg h₀ hbez hcv'
  have hmk := mk0_foldPipe hf hfdeg h₀ hbez hcv' hst.monicU
  rw [prod_mk0_foldXs_foldYs hcv, mul_one] at hmk
  have h := mumfordIdeal_reduced_unique f hst.monicU h₀.monicU hst.degree_V_lt
    h₀.degree_V_lt (by rw [hst.natDegree_U, hfdeg]; lia)
    (by rw [h₀.natDegree_U, hfdeg]; lia) hst.dvd_sq h₀.dvd_sq hmk
  exact Prod.ext h.1 h.2

/-- **Two fold pipelines whose inputs represent the same total class have the same output**: both
outputs are reduced representatives of that class. The engine of pack-independence and of the
class-group identities behind the group-law axioms of `F_τ`. -/
theorem fold_pipeline_eq_of_mk0_eq {xs' ys' : ℕ → K} {d' : ℕ → FoldTriple K}
    {U₀' V₀' : K[X]} {m m' : ℕ} (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (h₀ : IsFoldState g f U₀ V₀) (h₀' : IsFoldState g f U₀' V₀')
    (hbez : ∀ j < m, (d j).s₁ * (foldPipe f xs ys d U₀ V₀ j).1
      + (d j).s₂ * (X - C (xs j))
      + (d j).s₃ * ((foldPipe f xs ys d U₀ V₀ j).2 + C (ys j)) = 1)
    (hcv : ∀ j < m, ys j ^ 2 = f.eval (xs j))
    (hbez' : ∀ j < m', (d' j).s₁ * (foldPipe f xs' ys' d' U₀' V₀' j).1
      + (d' j).s₂ * (X - C (xs' j))
      + (d' j).s₃ * ((foldPipe f xs' ys' d' U₀' V₀' j).2 + C (ys' j)) = 1)
    (hcv' : ∀ j < m', ys' j ^ 2 = f.eval (xs' j))
    (hmk : ClassGroup.mk0 ⟨mumfordIdeal f U₀ V₀,
          mumfordIdeal_mem_nonZeroDivisors f h₀.monicU.ne_zero V₀⟩
        * ∏ j ∈ Finset.range m,
            ClassGroup.mk0 ⟨mumfordIdeal f (X - C (xs j)) (C (ys j)),
              mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C (xs j)).ne_zero
                (C (ys j))⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f U₀' V₀',
          mumfordIdeal_mem_nonZeroDivisors f h₀'.monicU.ne_zero V₀'⟩
        * ∏ j ∈ Finset.range m',
            ClassGroup.mk0 ⟨mumfordIdeal f (X - C (xs' j)) (C (ys' j)),
              mumfordIdeal_mem_nonZeroDivisors f (monic_X_sub_C (xs' j)).ne_zero
                (C (ys' j))⟩) :
    foldPipe f xs ys d U₀ V₀ m = foldPipe f xs' ys' d' U₀' V₀' m' := by
  have hst := isFoldState_foldPipe (m := m) hf hfdeg h₀ hbez hcv
  have hst' := isFoldState_foldPipe (m := m') hf hfdeg h₀' hbez' hcv'
  have hcl := (mk0_foldPipe hf hfdeg h₀ hbez hcv hst.monicU).trans
    (hmk.trans (mk0_foldPipe hf hfdeg h₀' hbez' hcv' hst'.monicU).symm)
  have h := mumfordIdeal_reduced_unique f hst.monicU hst'.monicU hst.degree_V_lt
    hst'.degree_V_lt (by rw [hst.natDegree_U, hfdeg]; lia)
    (by rw [hst'.natDegree_U, hfdeg]; lia) hst.dvd_sq hst'.dvd_sq hcl
  exact Prod.ext h.1 h.2

end ClassEngine

end ChabautyColeman

end
