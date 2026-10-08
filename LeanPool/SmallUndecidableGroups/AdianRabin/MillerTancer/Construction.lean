/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Presentation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Group

/-!
# Construction

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace MillerTancer

/-- Include an old generator among the first `n` generators of the new presentation. -/
def oldGenerator (i : Fin n) : Fin (n + 3) :=
  Fin.castAdd 3 i

/-- Include an old word in the enlarged alphabet. -/
def oldWord (w : Word n) : Word (n + 3) :=
  Word.mapGenerators oldGenerator w

/-- The three new words `α`, `β`, and `γ`. -/
def alphaWord (n : ℕ) : Word (n + 3) :=
  Word.generator (Fin.natAdd n 0)

/-- The word representing the generator `beta` in this presentation. -/
def betaWord (n : ℕ) : Word (n + 3) :=
  Word.generator (Fin.natAdd n 1)

/-- The word representing the generator `gamma` in this presentation. -/
def gammaWord (n : ℕ) : Word (n + 3) :=
  Word.generator (Fin.natAdd n 2)

/-- The relator `σ₁` in the Miller--Tancer presentation. -/
def sigma₁ (n : ℕ) : Word (n + 3) :=
  let alpha := alphaWord n
  let beta := betaWord n
  let gamma := gammaWord n
  Word.relation
    (Word.product [Word.inverse alpha, beta, alpha])
    (Word.product
      [Word.inverse gamma, Word.inverse beta, gamma, beta, gamma])

/-- The relator `σ₂` in the Miller--Tancer presentation. -/
def sigma₂ (n : ℕ) : Word (n + 3) :=
  let alpha := alphaWord n
  let beta := betaWord n
  let gamma := gammaWord n
  Word.relation
    (Word.product
      [Word.inverse (Word.pow alpha 2), Word.inverse beta, alpha, beta,
       Word.pow alpha 2])
    (Word.product
      [Word.inverse (Word.pow gamma 2), Word.inverse beta, gamma, beta,
       Word.pow gamma 2])

/-- The commutator relator `σ₃(w)` in the Miller--Tancer presentation;
see the correction discussed in Remark 1.9 of the paper. -/
def sigma₃ (w : Word n) : Word (n + 3) :=
  let alpha := alphaWord n
  let beta := betaWord n
  let gamma := gammaWord n
  Word.relation
    (Word.product
      [Word.inverse (Word.pow alpha 3),
       Word.commutator (oldWord w) beta,
       Word.pow alpha 3])
    (Word.product
      [Word.inverse (Word.pow gamma 3), beta, Word.pow gamma 3])

/-- The relator `σ₄(z)` in the Miller--Tancer presentation, using the
single normal generator `z`. -/
def sigma₄ (z : Word n) : Word (n + 3) :=
  let alpha := alphaWord n
  let beta := betaWord n
  let gamma := gammaWord n
  Word.relation
    (Word.product
      [Word.inverse (Word.pow alpha 2), oldWord z, beta,
       Word.pow alpha 4])
    (Word.product
      [Word.inverse (Word.pow gamma 4), beta, Word.pow gamma 4])

/-- The four additional Miller--Tancer relators. -/
def additionalRelators (z w : Word n) : Fin 4 → Word (n + 3) :=
  ![sigma₁ n, sigma₂ n, sigma₃ w, sigma₄ z]

/--
The Miller--Tancer transformation: retain the `m` old relators and add
three generators and four relators.
-/
def transform (P : FP n m) (z w : Word n) : FP (n + 3) (m + 4) where
  relator := Fin.append
    (fun i => oldWord (P.relator i))
    (additionalRelators z w)

@[simp]
theorem transform_old
    (P : FP n m) (z w : Word n) (i : Fin m) :
    (transform P z w).relator (Fin.castAdd 4 i) =
      oldWord (P.relator i) := by
  simp [transform]

@[simp]
theorem transform_additional
    (P : FP n m) (z w : Word n) (i : Fin 4) :
    (transform P z w).relator (Fin.natAdd m i) =
      additionalRelators z w i := by
  simp [transform]

/-- The word-indexed transformation is uniform and computable. -/
theorem transform_computable (P : FP n m) (z : Word n) :
    Computable₂ fun w i => (transform P z w).relator i := by
  have holdGenerator : Primrec (@oldGenerator n) := by
    apply Primrec.fin_val_iff.mp
    exact Primrec.fin_val
  have holdLetter : Primrec fun x : SignedGenerator n =>
      (oldGenerator x.1, x.2) :=
    Primrec.pair (holdGenerator.comp Primrec.fst) Primrec.snd
  have holdWord : Primrec (@oldWord n) := by
    apply Primrec.of_eq
      (Primrec.list_map Primrec.id (holdLetter.comp Primrec.snd).to₂)
    intro w
    rfl
  have hcommutator : Primrec fun u : Word (n + 3) =>
      Word.commutator u (betaWord n) := by
    apply Primrec.of_eq
      (Primrec.list_append.comp (Word.inverse_primrec (n + 3))
        (Primrec.list_append.comp
          (Primrec.const (Word.inverse (betaWord n)))
          (Primrec.list_append.comp Primrec.id
            (Primrec.const (betaWord n)))))
    intro u
    rfl
  have hmiddle : Primrec fun w : Word n =>
      Word.commutator (oldWord w) (betaWord n) :=
    hcommutator.comp holdWord
  let alpha := alphaWord n
  let beta := betaWord n
  let gamma := gammaWord n
  let lhs : Word n → Word (n + 3) := fun w =>
    Word.product
      [Word.inverse (Word.pow alpha 3),
       Word.commutator (oldWord w) beta,
       Word.pow alpha 3]
  let rhs : Word (n + 3) :=
    Word.product
      [Word.inverse (Word.pow gamma 3), beta, Word.pow gamma 3]
  have hlhs : Primrec lhs := by
    apply Primrec.of_eq
      (Primrec.list_append.comp
        (Primrec.const (Word.inverse (Word.pow alpha 3)))
        (Primrec.list_append.comp hmiddle
          (Primrec.const (Word.pow alpha 3))))
    intro w
    simp [lhs, Word.product, beta]
  have hsigma3 : Primrec (@sigma₃ n) := by
    apply Primrec.of_eq
      (Primrec.list_append.comp hlhs
        (Primrec.const (Word.inverse rhs)))
    intro w
    rfl
  apply Primrec₂.to_comp
  apply (Primrec.fin_curry).mp
  apply (Primrec.fin_curry).mpr
  apply Primrec₂.swap
  apply (Primrec.fin_curry₁).mpr
  intro i
  cases i using Fin.addCases with
  | left j =>
      simpa using
        (Primrec.const (α := Word n) (oldWord (P.relator j)))
  | right j =>
      refine Fin.cases ?_ (fun j3 => ?_) j
      · simpa [additionalRelators] using
          (Primrec.const (α := Word n) (sigma₁ n))
      · refine Fin.cases ?_ (fun j2 => ?_) j3
        · simpa [additionalRelators] using
            (Primrec.const (α := Word n) (sigma₂ n))
        · refine Fin.cases ?_ (fun j1 => ?_) j2
          · simpa [additionalRelators] using hsigma3
          · refine Fin.cases ?_ (fun j0 => ?_) j1
            · simpa [additionalRelators] using
                (Primrec.const (α := Word n) (sigma₄ z))
            · exact Fin.elim0 j0

private theorem exists_oldHom (P : FP n m) (z w : Word n) :
    ∃ f : P.Group →* (transform P z w).Group,
      ∀ i : Fin n,
        f (PresentedGroup.of i) = PresentedGroup.of (oldGenerator i) := by
  let x : Fin n → (transform P z w).Group :=
    fun i => PresentedGroup.of (oldGenerator i)
  have hrel : ∀ i, Word.eval x (P.relator i) = 1 := by
    intro i
    have h := (transform P z w).relator_eq_one (Fin.castAdd 4 i)
    simpa [FP.evalWord, oldWord, x, Function.comp_def] using h
  refine ⟨P.homOfRelators x hrel, ?_⟩
  intro i
  exact P.homOfRelators_of x hrel i

private theorem hom_eq_one_of_normallyGenerates
    (P : FP n m) (z : Word n) (hz : P.NormallyGenerates z)
    {G : Type*} [Group G] (f : P.Group →* G)
    (hf : f (PresentedGroup.mk P.relSet (FreeGroup.mk z)) = 1) :
    ∀ g : P.Group, f g = 1 := by
  have hclosure :
      Subgroup.normalClosure
          ({PresentedGroup.mk P.relSet (FreeGroup.mk z)} : Set P.Group) ≤
        f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact MonoidHom.mem_ker.mpr hf
  rw [hz] at hclosure
  intro g
  exact MonoidHom.mem_ker.mp (hclosure (Set.mem_univ g))

private theorem additional_relator_eq_one
    (P : FP n m) (z w : Word n) (i : Fin 4) :
    Word.eval
        (PresentedGroup.of : Fin (n + 3) → (transform P z w).Group)
        (additionalRelators z w i) = 1 := by
  simpa [FP.evalWord] using
    (transform P z w).relator_eq_one (Fin.natAdd m i)

/-- The elementary half of the Miller--Tancer argument. -/
theorem presentsTrivial_transform_of_wordProblem
    (P : FP n m) (z : Word n) (hz : P.NormallyGenerates z) (w : Word n)
    (hw : P.wordProblem w) :
    (transform P z w).presentsTrivial := by
  let x : Fin (n + 3) → (transform P z w).Group := PresentedGroup.of
  let a := x (Fin.natAdd n 0)
  let b := x (Fin.natAdd n 1)
  let c := x (Fin.natAdd n 2)
  obtain ⟨f, hf⟩ := exists_oldHom P z w
  have hwP : Word.eval (PresentedGroup.of : Fin n → P.Group) w = 1 :=
    (P.wordProblem_iff_evalWord_eq_one w).mp hw
  have hwT : Word.eval x (oldWord w) = 1 := by
    rw [oldWord, Word.eval_mapGenerators]
    calc
      Word.eval (fun i => x (oldGenerator i)) w =
          Word.eval (fun i => f (PresentedGroup.of i)) w := by
            congr 2
            funext i
            exact (hf i).symm
      _ = f (Word.eval (PresentedGroup.of : Fin n → P.Group) w) := by
            symm
            exact Word.map_eval f _ w
      _ = 1 := by rw [hwP, map_one]
  have h₁raw := additional_relator_eq_one P z w (0 : Fin 4)
  have h₂raw := additional_relator_eq_one P z w (1 : Fin 4)
  have h₃raw := additional_relator_eq_one P z w (2 : Fin 4)
  have h₄raw := additional_relator_eq_one P z w (3 : Fin 4)
  have h₁ : a⁻¹ * b * a = c⁻¹ * b⁻¹ * c * b * c := by
    apply eq_of_mul_inv_eq_one
    simpa only [Fin.isValue, mul_assoc, mul_inv_rev, inv_inv, additionalRelators, sigma₁,
      alphaWord, betaWord, gammaWord, Matrix.cons_val_zero, Word.eval_relation, Word.eval_product,
      List.map_cons, Word.eval_inverse, Word.eval_generator, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using h₁raw
  have h₂ :
      (a ^ 2)⁻¹ * b⁻¹ * a * b * a ^ 2 =
        (c ^ 2)⁻¹ * b⁻¹ * c * b * c ^ 2 := by
    apply eq_of_mul_inv_eq_one
    simpa only [Fin.isValue, mul_assoc, mul_inv_rev, inv_inv, additionalRelators, sigma₂,
      alphaWord, betaWord, gammaWord, Matrix.cons_val_one, Matrix.cons_val_zero,
      Word.eval_relation, Word.eval_product, List.map_cons, Word.eval_inverse, Word.eval_pow,
      Word.eval_generator, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h₂raw
  have h₃ :
      (a ^ 3)⁻¹ *
          ((Word.eval x (oldWord w))⁻¹ * b⁻¹ *
            Word.eval x (oldWord w) * b) * a ^ 3 =
        (c ^ 3)⁻¹ * b * c ^ 3 := by
    apply eq_of_mul_inv_eq_one
    simpa only [Fin.isValue, mul_assoc, mul_inv_rev, inv_inv, additionalRelators, sigma₃,
      alphaWord, betaWord, gammaWord, Matrix.cons_val, Word.eval_relation, Word.eval_product,
      List.map_cons, Word.eval_inverse, Word.eval_pow, Word.eval_generator, Word.eval_commutator,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h₃raw
  have h₄ :
      (a ^ 2)⁻¹ * Word.eval x (oldWord z) * b * a ^ 4 =
        (c ^ 4)⁻¹ * b * c ^ 4 := by
    apply eq_of_mul_inv_eq_one
    simpa only [Fin.isValue, mul_assoc, mul_inv_rev, inv_inv, additionalRelators, sigma₄,
      alphaWord, betaWord, gammaWord, Matrix.cons_val, Word.eval_relation, Word.eval_product,
      List.map_cons, Word.eval_inverse, Word.eval_pow, Word.eval_generator, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using h₄raw
  have hbConj : (c ^ 3)⁻¹ * b * c ^ 3 = 1 := by
    simpa [hwT] using h₃.symm
  have hb : b = 1 := by
    calc
      b = c ^ 3 * ((c ^ 3)⁻¹ * b * c ^ 3) * (c ^ 3)⁻¹ := by group
      _ = 1 := by rw [hbConj]; simp
  have hc : c = 1 := by
    simpa [hb] using h₁.symm
  have haConj : (a ^ 2)⁻¹ * a * a ^ 2 = 1 := by
    simpa [hb, hc] using h₂
  have ha : a = 1 := by
    calc
      a = (a ^ 2)⁻¹ * a * a ^ 2 := by group
      _ = 1 := haConj
  have hzT : Word.eval x (oldWord z) = 1 := by
    simpa [ha, hb, hc] using h₄
  have hfz : f (PresentedGroup.mk P.relSet (FreeGroup.mk z)) = 1 := by
    calc
      f (PresentedGroup.mk P.relSet (FreeGroup.mk z)) =
          f (Word.eval (PresentedGroup.of : Fin n → P.Group) z) :=
            congrArg f (P.evalWord_eq_mk z).symm
      _ = Word.eval (fun i => f (PresentedGroup.of i)) z := Word.map_eval f _ z
      _ = Word.eval (fun i => x (oldGenerator i)) z := by
            congr 2
            funext i
            exact hf i
      _ = Word.eval x (oldWord z) := by
            simp [oldWord, Function.comp_def]
      _ = 1 := hzT
  have hfOne : ∀ g : P.Group, f g = 1 :=
    hom_eq_one_of_normallyGenerates P z hz f hfz
  have hold : ∀ i : Fin n, x (oldGenerator i) = 1 := by
    intro i
    change PresentedGroup.of (oldGenerator i) = 1
    rw [← hf i]
    exact hfOne _
  have hx : ∀ i : Fin (n + 3), x i = 1 := by
    intro i
    refine Fin.addCases hold ?_ i
    intro j
    refine Fin.cases ha (fun j' => ?_) j
    refine Fin.cases hb (fun j'' => ?_) j'
    refine Fin.cases hc (fun j''' => ?_) j''
    exact Fin.elim0 j'''
  exact (transform P z w).presentsTrivial_of_generator_eq_one hx

end MillerTancer
end Undecidability
