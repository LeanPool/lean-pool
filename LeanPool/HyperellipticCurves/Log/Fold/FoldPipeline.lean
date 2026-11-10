/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorPipeline
public import LeanPool.HyperellipticCurves.Log.Fold.FoldChain

/-!
# The fold pipeline

The point-by-point pipeline of the fold construction of `F_τ`. Starting from a Mumford pair, it
adds one point per step by a Cantor composition at a Bézout triple followed by the
`(-1)`-normalized reduction — in the unconditional regime of the fold, the composed cofactor always
has leading coefficient `-1`, so each step returns to the generic degree and no reduction chains
are needed.

## Main definitions

* `ChabautyColeman.FoldTriple`, `ChabautyColeman.FoldCertData`: one Bézout triple per
  step — the entire certificate pack of the fold pipeline.
* `ChabautyColeman.foldPipeStep`, `ChabautyColeman.foldPipe`: the step and the pipeline
  recursion.

## Main statements

* `ChabautyColeman.isFoldState_foldPipe`: the stage invariants — with valid Bézout
  triples and points on the curve below the stage, every pipeline state is a fold state
  (monic support of degree exactly `g`, Mumford divisibility, reduced square root).
* `ChabautyColeman.map_foldPipe`: the pipeline commutes with base change.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### The fold pack -/

/-- **One Bézout triple of the fold pack**: the composition certificate of one step of
the point-by-point fold. -/
structure FoldTriple (S : Type*) [CommRing S] where
  /-- The coefficient of the current support. -/
  s₁ : S[X]
  /-- The coefficient of the added point's support. -/
  s₂ : S[X]
  /-- The coefficient of the square-root sum; zero at all disjoint steps. -/
  s₃ : S[X]

namespace FoldTriple

variable {S S' : Type*} [CommRing S] [CommRing S']

/-- Base change of a fold triple. -/
noncomputable def map (φ : S →+* S') (c : FoldTriple S) : FoldTriple S' :=
  ⟨c.s₁.map φ, c.s₂.map φ, c.s₃.map φ⟩

@[simp] theorem map_s₁ (φ : S →+* S') (c : FoldTriple S) : (c.map φ).s₁ = c.s₁.map φ := rfl

@[simp] theorem map_s₂ (φ : S →+* S') (c : FoldTriple S) : (c.map φ).s₂ = c.s₂.map φ := rfl

@[simp] theorem map_s₃ (φ : S →+* S') (c : FoldTriple S) : (c.map φ).s₃ = c.s₃.map φ := rfl

end FoldTriple

/-- **The fold pack**: one Bézout triple per step of the `2n`-step point-by-point fold. -/
def FoldCertData (S : Type*) [CommRing S] (n : ℕ) := Fin (2 * n) → FoldTriple S

/-- Base change of a fold pack. -/
noncomputable def FoldCertData.map {S S' : Type*} [CommRing S] [CommRing S'] (φ : S →+* S') {n : ℕ}
    (d : FoldCertData S n) : FoldCertData S' n :=
  fun j ↦ (d j).map φ

/-! ### The pipeline recursion -/

section Pipe

variable {S : Type*} [CommRing S]

/-- **One step of the fold pipeline**: Cantor composition with the point `(x, y)` at the
Bézout triple `c`, followed by the `(-1)`-normalized reduction (the unconditional regime:
the composed cofactor always has leading coefficient `-1`). -/
noncomputable def foldPipeStep (f : S[X]) (p : S[X] × S[X]) (x y : S) (c : FoldTriple S) :
    S[X] × S[X] :=
  cantorReduce f (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1
    (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).2 (-1)

/-- **The fold pipeline**: starting from the pair `(U₀, V₀)`, add the points
`(xs j, ys j)` one at a time along the pack of Bézout triples. -/
noncomputable def foldPipe (f : S[X]) (xs ys : ℕ → S) (d : ℕ → FoldTriple S)
    (U₀ V₀ : S[X]) : ℕ → S[X] × S[X]
  | 0 => (U₀, V₀)
  | j + 1 => foldPipeStep f (foldPipe f xs ys d U₀ V₀ j) (xs j) (ys j) (d j)

variable {f : S[X]} {xs ys : ℕ → S} {d : ℕ → FoldTriple S} {U₀ V₀ : S[X]}

@[simp] theorem foldPipe_zero : foldPipe f xs ys d U₀ V₀ 0 = (U₀, V₀) := rfl

theorem foldPipe_succ (j : ℕ) :
    foldPipe f xs ys d U₀ V₀ (j + 1)
      = foldPipeStep f (foldPipe f xs ys d U₀ V₀ j) (xs j) (ys j) (d j) := rfl

/-- The pipeline reads its inputs only below the stage. -/
theorem foldPipe_congr {xs' ys' : ℕ → S} {d' : ℕ → FoldTriple S} {m : ℕ}
    (hx : ∀ i < m, xs i = xs' i) (hy : ∀ i < m, ys i = ys' i)
    (hd : ∀ i < m, d i = d' i) :
    foldPipe f xs ys d U₀ V₀ m = foldPipe f xs' ys' d' U₀ V₀ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [foldPipe_succ, foldPipe_succ,
      ih (fun i hi ↦ hx i (by lia)) (fun i hi ↦ hy i (by lia)) fun i hi ↦ hd i (by lia),
      hx m (by lia), hy m (by lia), hd m (by lia)]

/-- A point on the curve, as a Mumford divisibility. -/
theorem X_sub_C_dvd_of_sq_eq {x y : S} (hcv : y ^ 2 = f.eval x) :
    (X - C x) ∣ (C y : S[X]) ^ 2 - f :=
  dvd_iff_isRoot.mpr (by simp [IsRoot, hcv])

/-- Points on the curve are preserved by base change. -/
theorem sq_eq_map_of_sq_eq {S' : Type*} [CommRing S'] (φ : S →+* S') {x y : S}
    (hcv : y ^ 2 = f.eval x) : φ y ^ 2 = (f.map φ).eval (φ x) := by
  rw [eval_map_apply, ← map_pow, hcv]

variable [Nontrivial S] {g : ℕ}

/-- The composed cofactor of a valid pipeline step has leading coefficient `-1` and
degree `g` (the unconditional regime) — so `(-1)` is a valid reduction certificate at
every step, which the class-level lemmas of `LeanPool.HyperellipticCurves.Log.Fold.FoldClass`
consume. -/
theorem foldPipeStep_cofactor_lc {p : S[X] × S[X]} {x y : S} {c : FoldTriple S}
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1) (hp : IsFoldState g f p.1 p.2)
    (hbez : c.s₁ * p.1 + c.s₂ * (X - C x) + c.s₃ * (p.2 + C y) = 1)
    (hcv : y ^ 2 = f.eval x) :
    (-1 : S) * (cantorCofactor f
        (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1
        (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).2).leadingCoeff = 1
      ∧ (cantorCofactor f (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1
          (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).2).natDegree = g := by
  have hqm : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1.Monic :=
    cantorCompose_monic f hp.monicU (monic_X_sub_C x)
  have hqdeg : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1.natDegree
      = g + 1 := by
    rw [cantorCompose_natDegree f hp.monicU (monic_X_sub_C x), hp.natDegree_U,
      natDegree_X_sub_C]
  have hqdvd := cantorCompose_dvd f hbez hp.dvd_sq (X_sub_C_dvd_of_sq_eq hcv)
  obtain ⟨hlc, hdegsum⟩ := leadingCoeff_natDegree_cantorCofactor f hf hfdeg hqm hqdeg
    hqdvd (cantorCompose_degree_lt f hp.monicU (monic_X_sub_C x)) (by lia)
  exact ⟨by rw [hlc]; ring, by lia⟩

/-- **One pipeline step preserves the fold-state invariants** (monic support of degree exactly `g`,
Mumford divisibility, reduced square root), given the step's Bézout identity and the added point on
the curve. -/
theorem isFoldState_foldPipeStep {p : S[X] × S[X]} {x y : S} {c : FoldTriple S}
    (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1) (hp : IsFoldState g f p.1 p.2)
    (hbez : c.s₁ * p.1 + c.s₂ * (X - C x) + c.s₃ * (p.2 + C y) = 1)
    (hcv : y ^ 2 = f.eval x) :
    IsFoldState g f (foldPipeStep f p x y c).1 (foldPipeStep f p x y c).2 := by
  have hqm : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1.Monic :=
    cantorCompose_monic f hp.monicU (monic_X_sub_C x)
  have hqdvd := cantorCompose_dvd f hbez hp.dvd_sq (X_sub_C_dvd_of_sq_eq hcv)
  obtain ⟨hc, hdeg⟩ := foldPipeStep_cofactor_lc hf hfdeg hp hbez hcv
  have hnat : (cantorReduce f (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1
      (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).2 (-1)).1.natDegree = g := by
    change (C (-1) * cantorCofactor f _ _).natDegree = g
    rwa [natDegree_C_mul_cofactor hc]
  refine ⟨cantorReduce_monic f hc, hnat, cantorReduce_dvd f hqm hqdvd hc, ?_⟩
  have h := cantorReduce_degree_lt f hc
  rwa [degree_eq_natDegree (cantorReduce_monic f hc).ne_zero, hnat] at h

/-- **The stage invariants of the fold pipeline**: with valid Bézout triples and points on the
curve below the stage, every pipeline state is a fold state. -/
theorem isFoldState_foldPipe (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (h₀ : IsFoldState g f U₀ V₀) {m : ℕ}
    (hbez : ∀ j < m, (d j).s₁ * (foldPipe f xs ys d U₀ V₀ j).1
      + (d j).s₂ * (X - C (xs j))
      + (d j).s₃ * ((foldPipe f xs ys d U₀ V₀ j).2 + C (ys j)) = 1)
    (hcv : ∀ j < m, ys j ^ 2 = f.eval (xs j)) :
    IsFoldState g f (foldPipe f xs ys d U₀ V₀ m).1 (foldPipe f xs ys d U₀ V₀ m).2 := by
  induction m with
  | zero => exact h₀
  | succ m ih =>
    exact isFoldState_foldPipeStep hf hfdeg
      (ih (fun j hj ↦ hbez j (by lia)) fun j hj ↦ hcv j (by lia))
      (hbez m (by lia)) (hcv m (by lia))

/-- One pipeline step commutes with base change (along the step's validity). -/
theorem map_foldPipeStep {S' : Type*} [CommRing S'] (φ : S →+* S') {p : S[X] × S[X]}
    {x y : S} {c : FoldTriple S} (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (hp : IsFoldState g f p.1 p.2)
    (hbez : c.s₁ * p.1 + c.s₂ * (X - C x) + c.s₃ * (p.2 + C y) = 1)
    (hcv : y ^ 2 = f.eval x) :
    ((foldPipeStep f p x y c).1.map φ, (foldPipeStep f p x y c).2.map φ)
      = foldPipeStep (f.map φ) (p.1.map φ, p.2.map φ) (φ x) (φ y) (c.map φ) := by
  have hqm : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1.Monic :=
    cantorCompose_monic f hp.monicU (monic_X_sub_C x)
  obtain ⟨hc, -⟩ := foldPipeStep_cofactor_lc hf hfdeg hp hbez hcv
  have hcomp := map_cantorCompose φ f hp.monicU (monic_X_sub_C x) p.2 (C y) c.s₁ c.s₂ c.s₃
  simp only [Polynomial.map_sub, Polynomial.map_X, map_C] at hcomp
  have hred := map_cantorReduce φ f hqm hc
  simp only [map_neg, map_one] at hred
  have hcomp1 : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).1.map φ
      = (cantorCompose (f.map φ) (p.1.map φ) (p.2.map φ) (X - C (φ x)) (C (φ y))
          (c.s₁.map φ) (c.s₂.map φ) (c.s₃.map φ)).1 := congrArg Prod.fst hcomp
  have hcomp2 : (cantorCompose f p.1 p.2 (X - C x) (C y) c.s₁ c.s₂ c.s₃).2.map φ
      = (cantorCompose (f.map φ) (p.1.map φ) (p.2.map φ) (X - C (φ x)) (C (φ y))
          (c.s₁.map φ) (c.s₂.map φ) (c.s₃.map φ)).2 := congrArg Prod.snd hcomp
  simp only [foldPipeStep, FoldTriple.map_s₁, FoldTriple.map_s₂, FoldTriple.map_s₃]
  rwa [← hcomp1, ← hcomp2]

/-- **The fold pipeline commutes with base change** along its stage validity. -/
theorem map_foldPipe {S' : Type*} [CommRing S'] (φ : S →+* S') (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (h₀ : IsFoldState g f U₀ V₀) {m : ℕ}
    (hbez : ∀ j < m, (d j).s₁ * (foldPipe f xs ys d U₀ V₀ j).1
      + (d j).s₂ * (X - C (xs j))
      + (d j).s₃ * ((foldPipe f xs ys d U₀ V₀ j).2 + C (ys j)) = 1)
    (hcv : ∀ j < m, ys j ^ 2 = f.eval (xs j)) :
    ((foldPipe f xs ys d U₀ V₀ m).1.map φ, (foldPipe f xs ys d U₀ V₀ m).2.map φ)
      = foldPipe (f.map φ) (fun j ↦ φ (xs j)) (fun j ↦ φ (ys j)) (fun j ↦ (d j).map φ)
        (U₀.map φ) (V₀.map φ) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hprev := isFoldState_foldPipe (m := m) hf hfdeg h₀
      (fun j hj ↦ hbez j (by lia)) fun j hj ↦ hcv j (by lia)
    have hstep := map_foldPipeStep φ hf hfdeg hprev (hbez m (by lia)) (hcv m (by lia))
    rw [foldPipe_succ, hstep, foldPipe_succ,
      ← ih (fun j hj ↦ hbez j (by lia)) fun j hj ↦ hcv j (by lia)]

end Pipe

end ChabautyColeman

end
