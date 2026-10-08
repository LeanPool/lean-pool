/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.AdianRabin.MillerTancer.Embedding
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Group

/-!
# The compressed Miller--Tancer construction

When the normally generating word is a displayed generator `x_k`, the
relations `σ₁` and `σ₄(x_k)` permit two further uniform Tietze
eliminations.  The resulting presentation has `n + 1` generators and
`m + 2` relators and presents the same group as the raw construction.
-/

@[expose] public section

namespace Undecidability.MillerTancer

/-- The raw Miller--Tancer triviality criterion. -/
theorem presentsTrivial_transform_iff
    (P : FP n m) (z : Word n)
    (hz : P.NormallyGenerates z) (w : Word n) :
    (transform P z w).presentsTrivial ↔ P.wordProblem w := by
  constructor
  · intro htrivial
    by_contra hw
    exact transform_not_trivial_of_not_wordProblem P z w hw htrivial
  · exact presentsTrivial_transform_of_wordProblem P z hz w

end Undecidability.MillerTancer

namespace Undecidability.MillerTancer.Compressed

/-- The slot retaining an original generator in the compressed presentation. -/
def finalOldSlot (i : Fin n) : Fin (n + 1) := i.castSucc

/-- The word representing the generator `b` in this presentation. -/
def bWord (k : Fin n) : Word (n + 1) := Word.generator (finalOldSlot k)
/-- The word representing the new compression generator `q`. -/
def qWord (n : ℕ) : Word (n + 1) := Word.generator (Fin.last n)
/-- The word representing the element `c` after the indicated substitutions. -/
def cWord (k : Fin n) : Word (n + 1) :=
  Word.product [bWord k, qWord n, bWord k, Word.inverse (qWord n), Word.inverse (bWord k)]
/-- The word representing the generator `a` in this presentation. -/
def aWord (k : Fin n) : Word (n + 1) :=
  Word.product [Word.inverse (qWord n), cWord k]
/-- The substitution word for the original generator eliminated by the compression. -/
def eliminatedWord (k : Fin n) : Word (n + 1) :=
  Word.product [Word.pow (aWord k) 2, Word.inverse (Word.pow (cWord k) 4),
    bWord k, Word.pow (cWord k) 4, Word.inverse (Word.pow (aWord k) 4),
    Word.inverse (bWord k)]

/-- The substitution for an original generator, eliminating the distinguished one. -/
def encodedOldGenerator (k : Fin n) (i : Fin n) : Word (n + 1) :=
  if i = k then eliminatedWord k else Word.generator (finalOldSlot i)

/-- The generator substitution performing the ordered Tietze eliminations. -/
def thetaGenerator (k : Fin n) : Fin (n + 3) → Word (n + 1) :=
  Fin.addCases (encodedOldGenerator k) ![aWord k, bWord k, cWord k]

/-- Extend the Tietze generator substitution to an arbitrary word. -/
def thetaWord (k : Fin n) (w : Word (n + 3)) : Word (n + 1) :=
  Word.substitute (thetaGenerator k) w

/-- The two additional relators retained after eliminating the redundant relations. -/
def keptAdditionalIndex : Fin 2 → Fin 4 := ![1, 2]

/-- The indices of the original and additional relators retained by the compression. -/
def retainedIndex (m : ℕ) : Fin (m + 2) → Fin (m + 4) :=
  Fin.addCases (fun i => Fin.castAdd 4 i)
    (fun j => Fin.natAdd m (keptAdditionalIndex j))

/-- The presentation retaining the original relators and two additional relations after generator
elimination. -/
def transform (P : FP n m) (k : Fin n) (w : Word n) : FP (n + 1) (m + 2) where
  relator i :=
    thetaWord k ((MillerTancer.transform P (Word.generator k) w).relator (retainedIndex m i))

@[simp] theorem retainedIndex_old (i : Fin m) :
 retainedIndex m (Fin.castAdd 2 i) = Fin.castAdd 4 i := by simp [retainedIndex]
@[simp] theorem retainedIndex_additional (j : Fin 2) :
 retainedIndex m (Fin.natAdd m j) = Fin.natAdd m (keptAdditionalIndex j) := by simp [retainedIndex]

@[simp] theorem transform_old (P : FP n m) (k : Fin n) (w : Word n) (i : Fin m) :
 (transform P k w).relator (Fin.castAdd 2 i) =
   thetaWord k (MillerTancer.oldWord (P.relator i)) := by
 simp [transform]

@[simp] theorem transform_additional (P : FP n m) (k : Fin n) (w : Word n) (j : Fin 2) :
 (transform P k w).relator (Fin.natAdd m j) =
   thetaWord k (MillerTancer.additionalRelators (Word.generator k) w (keptAdditionalIndex j)) := by
 simp [transform]

theorem thetaWord_primrec (k : Fin n) : Primrec (thetaWord k) := by
  have hgenerator : Primrec (thetaGenerator k) := Primrec.dom_finite _
  have hletter : Primrec fun x : SignedGenerator (n + 3) =>
      bif x.2 then thetaGenerator k x.1 else Word.inverse (thetaGenerator k x.1) :=
    Primrec.cond Primrec.snd (hgenerator.comp Primrec.fst)
      ((Word.inverse_primrec (n + 1)).comp (hgenerator.comp Primrec.fst))
  apply Primrec.of_eq
    (Primrec.list_flatMap Primrec.id (hletter.comp Primrec.snd).to₂)
  intro w
  simp only [thetaWord, Word.substitute]
  congr 1
  funext x
  cases x.2 <;> rfl

theorem transform_computable (P : FP n m) (k : Fin n) :
    Computable₂ fun w i => (transform P k w).relator i := by
  have hindex : Computable (retainedIndex m) := (Primrec.dom_finite _).to_comp
  have hraw : Computable fun p : Word n × Fin (m + 2) =>
      (MillerTancer.transform P (Word.generator k) p.1).relator
        (retainedIndex m p.2) :=
    (MillerTancer.transform_computable P (Word.generator k)).comp
      Computable.fst (hindex.comp Computable.snd)
  exact ((thetaWord_primrec k).to_comp.comp hraw).to₂

@[simp] theorem eval_thetaWord {G : Type*} [Group G]
    (x : Fin (n + 1) → G) (k : Fin n) (w : Word (n + 3)) :
    Word.eval x (thetaWord k w) =
      Word.eval (fun i => Word.eval x (thetaGenerator k i)) w :=
  Word.eval_substitute x (thetaGenerator k) w

@[simp] theorem thetaGenerator_old (k : Fin n) (i : Fin n) :
 thetaGenerator k (MillerTancer.oldGenerator i) = encodedOldGenerator k i := by
 simp [thetaGenerator, MillerTancer.oldGenerator]

@[simp] private theorem thetaGenerator_alpha (k : Fin n) :
    thetaGenerator k (Fin.natAdd n 0) = aWord k := by
  simp [thetaGenerator]

@[simp] private theorem thetaGenerator_beta (k : Fin n) :
    thetaGenerator k (Fin.natAdd n 1) = bWord k := by
  simp [thetaGenerator]

@[simp] private theorem thetaGenerator_gamma (k : Fin n) :
    thetaGenerator k (Fin.natAdd n 2) = cWord k := by
  simp [thetaGenerator]

theorem theta_sigma₁_eval_one {G : Type*} [Group G]
    (x : Fin (n + 1) → G) (k : Fin n) :
    Word.eval x (thetaWord k (MillerTancer.sigma₁ n)) = 1 := by
  rw [eval_thetaWord]
  simp only [MillerTancer.sigma₁, MillerTancer.alphaWord,
    MillerTancer.betaWord, MillerTancer.gammaWord,
    aWord, bWord, cWord, qWord, finalOldSlot, Word.eval_relation,
    Word.eval_product, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Word.eval_inverse, Word.eval_generator, thetaGenerator_alpha,
    thetaGenerator_beta, thetaGenerator_gamma]
  group

theorem theta_sigma₄_eval_one {G : Type*} [Group G]
    (x : Fin (n + 1) → G) (k : Fin n) :
    Word.eval x
      (thetaWord k (MillerTancer.sigma₄ (Word.generator k))) = 1 := by
  rw [eval_thetaWord]
  simp [thetaGenerator, encodedOldGenerator, MillerTancer.sigma₄,
    MillerTancer.alphaWord, MillerTancer.betaWord, MillerTancer.gammaWord,
    MillerTancer.oldWord, MillerTancer.oldGenerator,
    aWord, bWord, cWord, qWord, eliminatedWord, finalOldSlot,
    Word.product, mul_assoc]

/-- The homomorphism from the original presentation to its compressed presentation. -/
def forwardHom (P : FP n m) (k : Fin n) (w : Word n) :
    (MillerTancer.transform P (Word.generator k) w).Group →*
      (Compressed.transform P k w).Group := by
  let y : Fin (n + 3) → (Compressed.transform P k w).Group :=
    fun i => Word.eval PresentedGroup.of (thetaGenerator k i)
  refine (MillerTancer.transform P (Word.generator k) w).homOfRelators y ?_
  intro i
  cases i using Fin.addCases with
  | left i =>
      simp only [MillerTancer.transform_old]
      dsimp only [y]
      rw [← eval_thetaWord]
      have h := (Compressed.transform P k w).relator_eq_one (Fin.castAdd 2 i)
      change Word.eval PresentedGroup.of
        ((Compressed.transform P k w).relator (Fin.castAdd 2 i)) = 1 at h
      simpa using h
  | right j =>
      fin_cases j
      · simp only [MillerTancer.transform_additional]
        dsimp only [y]
        change Word.eval (fun i => Word.eval PresentedGroup.of (thetaGenerator k i))
          (MillerTancer.sigma₁ n) = 1
        rw [← eval_thetaWord]
        exact theta_sigma₁_eval_one PresentedGroup.of k
      · rw [← eval_thetaWord]
        have h := (Compressed.transform P k w).relator_eq_one
          (Fin.natAdd m (0 : Fin 2))
        change Word.eval PresentedGroup.of
          ((Compressed.transform P k w).relator (Fin.natAdd m (0 : Fin 2))) = 1 at h
        simpa [y, keptAdditionalIndex] using h
      · rw [← eval_thetaWord]
        have h := (Compressed.transform P k w).relator_eq_one
          (Fin.natAdd m (1 : Fin 2))
        change Word.eval PresentedGroup.of
          ((Compressed.transform P k w).relator (Fin.natAdd m (1 : Fin 2))) = 1 at h
        simpa [y, keptAdditionalIndex] using h
      · simp only [MillerTancer.transform_additional]
        dsimp only [y]
        change Word.eval (fun i => Word.eval PresentedGroup.of (thetaGenerator k i))
          (MillerTancer.sigma₄ (Word.generator k)) = 1
        rw [← eval_thetaWord]
        exact theta_sigma₄_eval_one PresentedGroup.of k

@[simp] private theorem forwardHom_of (P : FP n m) (k : Fin n) (w : Word n)
    (i : Fin (n + 3)) :
    forwardHom P k w (PresentedGroup.of i) =
      Word.eval PresentedGroup.of (thetaGenerator k i) := by
  simp [forwardHom]

/-- The original-group interpretations of the generators of the compressed presentation. -/
def reverseGenerator (P : FP n m) (k : Fin n) (w : Word n) :
    Fin (n + 1) → (MillerTancer.transform P (Word.generator k) w).Group :=
  let x : Fin (n + 3) → (MillerTancer.transform P (Word.generator k) w).Group :=
    PresentedGroup.of
  Fin.lastCases
    (x (Fin.natAdd n 2) * (x (Fin.natAdd n 0))⁻¹)
    (fun i => if i = k then x (Fin.natAdd n 1) else x (MillerTancer.oldGenerator i))

private theorem raw_sigma₁_eq (P : FP n m) (k : Fin n) (w : Word n) :
    let x : Fin (n + 3) → (MillerTancer.transform P (Word.generator k) w).Group :=
      PresentedGroup.of
    let a := x (Fin.natAdd n 0)
    let b := x (Fin.natAdd n 1)
    let c := x (Fin.natAdd n 2)
    a⁻¹ * b * a = c⁻¹ * b⁻¹ * c * b * c := by
  dsimp only
  have h := (MillerTancer.transform P (Word.generator k) w).relator_eq_one
    (Fin.natAdd m (0 : Fin 4))
  change Word.eval PresentedGroup.of
    ((MillerTancer.transform P (Word.generator k) w).relator
      (Fin.natAdd m (0 : Fin 4))) = 1 at h
  rw [MillerTancer.transform_additional] at h
  apply eq_of_mul_inv_eq_one
  simpa [MillerTancer.additionalRelators, MillerTancer.sigma₁,
    MillerTancer.alphaWord, MillerTancer.betaWord, MillerTancer.gammaWord,
    Word.product, mul_assoc] using h

private theorem raw_sigma₄_eq (P : FP n m) (k : Fin n) (w : Word n) :
    let x : Fin (n + 3) → (MillerTancer.transform P (Word.generator k) w).Group :=
      PresentedGroup.of
    let a := x (Fin.natAdd n 0)
    let b := x (Fin.natAdd n 1)
    let c := x (Fin.natAdd n 2)
    let z := x (MillerTancer.oldGenerator k)
    (a ^ 2)⁻¹ * z * b * a ^ 4 = (c ^ 4)⁻¹ * b * c ^ 4 := by
  dsimp only
  have h := (MillerTancer.transform P (Word.generator k) w).relator_eq_one
    (Fin.natAdd m (3 : Fin 4))
  change Word.eval PresentedGroup.of
    ((MillerTancer.transform P (Word.generator k) w).relator
      (Fin.natAdd m (3 : Fin 4))) = 1 at h
  rw [MillerTancer.transform_additional] at h
  apply eq_of_mul_inv_eq_one
  simpa [MillerTancer.additionalRelators, MillerTancer.sigma₄,
    MillerTancer.alphaWord, MillerTancer.betaWord, MillerTancer.gammaWord,
    MillerTancer.oldWord, MillerTancer.oldGenerator,
    Word.product, mul_assoc] using h

theorem eval_thetaGenerator_reverse (P : FP n m) (k : Fin n) (w : Word n)
    (i : Fin (n + 3)) :
    Word.eval (reverseGenerator P k w) (thetaGenerator k i) =
      (PresentedGroup.of i : (MillerTancer.transform P (Word.generator k) w).Group) := by
  let x : Fin (n + 3) → (MillerTancer.transform P (Word.generator k) w).Group :=
    PresentedGroup.of
  let a := x (Fin.natAdd n 0)
  let b := x (Fin.natAdd n 1)
  let c := x (Fin.natAdd n 2)
  let q := c * a⁻¹
  have h₁ := raw_sigma₁_eq P k w
  change a⁻¹ * b * a = c⁻¹ * b⁻¹ * c * b * c at h₁
  have hC : b * q * b * q⁻¹ * b⁻¹ = c := by
    dsimp only [q]
    calc
      b * (c * a⁻¹) * b * (c * a⁻¹)⁻¹ * b⁻¹ =
          b * c * (a⁻¹ * b * a) * c⁻¹ * b⁻¹ := by group
      _ = c := by rw [h₁]; group
  have hA : q⁻¹ * (b * q * b * q⁻¹ * b⁻¹) = a := by
    rw [hC]
    dsimp only [q]
    group
  have h₄ := raw_sigma₄_eq P k w
  change (a ^ 2)⁻¹ * x (MillerTancer.oldGenerator k) * b * a ^ 4 =
    (c ^ 4)⁻¹ * b * c ^ 4 at h₄
  have hU : a ^ 2 * (c ^ 4)⁻¹ * b * c ^ 4 * (a ^ 4)⁻¹ * b⁻¹ =
      x (MillerTancer.oldGenerator k) := by
    calc
      a ^ 2 * (c ^ 4)⁻¹ * b * c ^ 4 * (a ^ 4)⁻¹ * b⁻¹ =
          a ^ 2 * ((c ^ 4)⁻¹ * b * c ^ 4) * (a ^ 4)⁻¹ * b⁻¹ := by group
      _ =
          a ^ 2 * ((a ^ 2)⁻¹ * x (MillerTancer.oldGenerator k) * b * a ^ 4) *
            (a ^ 4)⁻¹ * b⁻¹ := by rw [← h₄]
      _ = x (MillerTancer.oldGenerator k) := by group
  let psi := reverseGenerator P k w
  have hbEval : Word.eval psi (bWord k) = b := by
    simp [psi, reverseGenerator, bWord, finalOldSlot, b, x]
  have hqEval : Word.eval psi (qWord n) = q := by
    simp [psi, reverseGenerator, qWord, q, a, c, x]
  have hcEval : Word.eval psi (cWord k) = c := by
    simp [cWord, Word.product, hbEval, hqEval]
    simpa only [mul_assoc] using hC
  have haEval : Word.eval psi (aWord k) = a := by
    simp only [aWord, Word.product, List.flatten_cons, List.flatten_nil, List.append_nil,
      Word.eval_append, Word.eval_inverse, hqEval, hcEval]
    rw [← hC]
    exact hA
  have huEval : Word.eval psi (eliminatedWord k) = x (MillerTancer.oldGenerator k) := by
    simp [eliminatedWord, Word.product, haEval, hbEval, hcEval]
    simpa only [mul_assoc] using hU
  change Word.eval psi (thetaGenerator k i) = x i
  cases i using Fin.addCases with
  | left i =>
      by_cases hik : i = k
      · subst i
        change Word.eval psi (thetaGenerator k (MillerTancer.oldGenerator k)) =
          x (MillerTancer.oldGenerator k)
        rw [thetaGenerator_old]
        simp only [encodedOldGenerator, ite_eq_left]
        exact huEval
      · simp [thetaGenerator, encodedOldGenerator, hik, finalOldSlot,
          psi, reverseGenerator, MillerTancer.oldGenerator, x]
  | right j =>
      fin_cases j
      · simpa [thetaGenerator] using haEval
      · simpa [thetaGenerator] using hbEval
      · simpa [thetaGenerator] using hcEval

/-- The homomorphism interpreting the compressed presentation in the original group. -/
def reverseHom (P : FP n m) (k : Fin n) (w : Word n) :
    (Compressed.transform P k w).Group →*
      (MillerTancer.transform P (Word.generator k) w).Group := by
  let psi := reverseGenerator P k w
  refine (Compressed.transform P k w).homOfRelators psi ?_
  intro i
  rw [show (Compressed.transform P k w).relator i =
    thetaWord k ((MillerTancer.transform P (Word.generator k) w).relator
      (retainedIndex m i)) from rfl]
  rw [eval_thetaWord]
  have heval : (fun j => Word.eval psi (thetaGenerator k j)) =
      (PresentedGroup.of : Fin (n + 3) →
        (MillerTancer.transform P (Word.generator k) w).Group) := by
    funext j
    exact eval_thetaGenerator_reverse P k w j
  rw [heval]
  have h := (MillerTancer.transform P (Word.generator k) w).relator_eq_one
    (retainedIndex m i)
  change Word.eval PresentedGroup.of
    ((MillerTancer.transform P (Word.generator k) w).relator
      (retainedIndex m i)) = 1 at h
  exact h

@[simp] private theorem reverseHom_of (P : FP n m) (k : Fin n) (w : Word n)
    (i : Fin (n + 1)) :
    reverseHom P k w (PresentedGroup.of i) = reverseGenerator P k w i := by
  simp [reverseHom]

theorem reverse_forward (P : FP n m) (k : Fin n) (w : Word n) :
    (reverseHom P k w).comp (forwardHom P k w) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply, forwardHom_of, Word.map_eval]
  have hfun : (⇑(reverseHom P k w) ∘
      (PresentedGroup.of : Fin (n + 1) → (Compressed.transform P k w).Group)) =
      reverseGenerator P k w := by
    funext j
    exact reverseHom_of P k w j
  rw [hfun]
  exact eval_thetaGenerator_reverse P k w i

theorem forward_reverse (P : FP n m) (k : Fin n) (w : Word n) :
    (forwardHom P k w).comp (reverseHom P k w) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  cases i using Fin.lastCases with
  | last =>
      rw [MonoidHom.comp_apply, reverseHom_of]
      simp [reverseGenerator, map_mul, forwardHom_of, thetaGenerator,
        aWord, bWord, cWord, qWord, finalOldSlot, Word.product, mul_assoc]
  | cast i =>
      by_cases hik : i = k
      · subst i
        rw [MonoidHom.comp_apply, reverseHom_of]
        simp [reverseGenerator, forwardHom_of, thetaGenerator,
          bWord, finalOldSlot]
      · rw [MonoidHom.comp_apply, reverseHom_of]
        simp [reverseGenerator, forwardHom_of, thetaGenerator,
          encodedOldGenerator, hik, finalOldSlot, MillerTancer.oldGenerator]

/-- The compressed presentation is isomorphic to the raw Miller--Tancer presentation. -/
def transformEquiv (P : FP n m) (k : Fin n) (w : Word n) :
    (MillerTancer.transform P (Word.generator k) w).Group ≃*
      (Compressed.transform P k w).Group :=
  MonoidHom.toMulEquiv (forwardHom P k w) (reverseHom P k w)
    (reverse_forward P k w) (forward_reverse P k w)

/-- Compression preserves the presented group, hence triviality. -/
theorem presentsTrivial_transform_iff_raw (P : FP n m) (k : Fin n) (w : Word n) :
    (Compressed.transform P k w).presentsTrivial ↔
      (MillerTancer.transform P (Word.generator k) w).presentsTrivial := by
  rw [FP.presentsTrivial_iff_subsingleton, FP.presentsTrivial_iff_subsingleton]
  exact (transformEquiv P k w).toEquiv.subsingleton_congr.symm

/-- The compressed Miller--Tancer triviality criterion. -/
theorem presentsTrivial_transform_iff (P : FP n m) (k : Fin n)
    (hk : P.NormallyGenerates (Word.generator k)) (w : Word n) :
    (Compressed.transform P k w).presentsTrivial ↔ P.wordProblem w := by
  rw [presentsTrivial_transform_iff_raw]
  exact MillerTancer.presentsTrivial_transform_iff
    P (Word.generator k) hk w

end Undecidability.MillerTancer.Compressed
