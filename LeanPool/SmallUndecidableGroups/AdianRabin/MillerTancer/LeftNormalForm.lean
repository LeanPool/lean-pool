/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.GroupTheory.CoprodILemmas
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-! Normal-form infrastructure for the left separated-conjugates map. -/

@[expose] public section

namespace Undecidability.MillerTancer.LeftNormalForm

open Monoid

theorem FreeGroup.lift_injective_of_coprodI_neWord
    {I : Type} {Q : Type} [Group Q] (a : I → Q)
    (hne : ∀ i j
      (u : CoprodI.NeWord (fun _ : I ↦ FreeGroup Unit) i j),
      CoprodI.lift (fun i ↦ FreeGroup.lift fun _ ↦ a i) u.prod ≠ 1) :
    Function.Injective (FreeGroup.lift a) := by
  have hlift : FreeGroup.lift a =
      (CoprodI.lift fun i ↦ FreeGroup.lift fun _ ↦ a i).comp
        (@freeGroupEquivCoprodI I).toMonoidHom := by
    ext i
    simp
  rw [hlift, MonoidHom.coe_comp]
  exact Function.Injective.comp
    (CoprodI.lift_injective_of_neWord_nontrivial _ hne)
    (@freeGroupEquivCoprodI I).injective

/-- A list-of-nonzero-powers formulation of the normal-form criterion.  This
is the form used by the separated-conjugates calculation: adjacent runs use
different proposed basis elements. -/
theorem FreeGroup.lift_injective_of_reduced_zpow_products
    {I : Type} {Q : Type} [Group Q] (a : I → Q)
    (hprod : ∀ l : List (I × ℤ), l ≠ [] →
      (∀ p ∈ l, p.2 ≠ 0) →
      l.IsChain (fun p q ↦ p.1 ≠ q.1) →
      (l.map fun p ↦ a p.1 ^ p.2).prod ≠ 1) :
    Function.Injective (FreeGroup.lift a) := by
  apply FreeGroup.lift_injective_of_coprodI_neWord a
  intro i j u
  let encode : (Σ _ : I, FreeGroup Unit) → I × ℤ :=
    fun s ↦ (s.1, FreeGroup.freeGroupUnitEquivInt s.2)
  let l := u.toList.map encode
  have hlne : l ≠ [] := by
    simpa [l] using u.toList_ne_nil
  have hlexp : ∀ p ∈ l, p.2 ≠ 0 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨s, hs, rfl⟩
    intro heq
    have hsone : s.2 = 1 :=
      FreeGroup.freeGroupUnitEquivInt.injective (by
        simpa [encode, FreeGroup.freeGroupUnitEquivInt] using heq)
    exact u.toWord.ne_one s hs hsone
  have hlchain : l.IsChain (fun p q ↦ p.1 ≠ q.1) := by
    change (u.toList.map encode).IsChain (fun p q ↦ p.1 ≠ q.1)
    rw [List.isChain_map]
    exact u.toWord.chain_ne.imp (by
      intro p q hpq
      simpa [encode] using hpq)
  have heval :
      (CoprodI.lift fun i ↦ FreeGroup.lift fun _ ↦ a i) u.prod =
        (l.map fun p ↦ a p.1 ^ p.2).prod := by
    simp only [CoprodI.NeWord.prod, CoprodI.Word.prod, map_list_prod,
      List.map_map, l, encode]
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [Function.comp_apply, CoprodI.lift_of]
    have hreconstruct :
        FreeGroup.of () ^ FreeGroup.freeGroupUnitEquivInt s.2 = s.2 :=
      FreeGroup.freeGroupUnitEquivInt.symm_apply_apply s.2
    calc
      FreeGroup.lift (fun _ ↦ a s.1) s.2 =
          FreeGroup.lift (fun _ ↦ a s.1)
            (FreeGroup.of () ^ FreeGroup.freeGroupUnitEquivInt s.2) := by
              rw [hreconstruct]
      _ = a s.1 ^ FreeGroup.freeGroupUnitEquivInt s.2 := by
        rw [map_zpow, FreeGroup.lift_apply_of]
  rw [heval]
  exact hprod l hlne hlexp hlchain

/-- The labels of the original group and the two cyclic factors. -/
inductive LeftIndex
  | old
  | alpha
  | beta
  deriving DecidableEq

/-- The original group or cyclic group corresponding to a left-factor label. -/
def LeftFactor (G : Type) : LeftIndex → Type
  | .old => G
  | .alpha => FreeGroup Unit
  | .beta => FreeGroup Unit

variable {G : Type} [Group G]

instance leftFactorGroup : ∀ i, Group (LeftFactor G i) := fun i => by
  cases i <;> simp only [LeftFactor] <;> infer_instance

/-- The indexed free product separating the original group and the cyclic factors. -/
abbrev LeftProduct (G : Type) [Group G] := CoprodI (LeftFactor G)

/-- The inclusion of the original group into the indexed free product. -/
def old (g : G) : LeftProduct G := CoprodI.of (i := LeftIndex.old) g

/-- The generator of the cyclic factor labeled `alpha`. -/
def alpha : LeftProduct G :=
  CoprodI.of (i := LeftIndex.alpha) (FreeGroup.of ())

/-- The generator `beta` in Miller–Tancer’s left normal form construction. -/
def beta : LeftProduct G :=
  CoprodI.of (i := LeftIndex.beta) (FreeGroup.of ())

private theorem of_ne_one {i : LeftIndex} {x : LeftFactor G i} (hx : x ≠ 1) :
    CoprodI.of x ≠ (1 : LeftProduct G) := by
  intro h
  apply hx
  apply CoprodI.of_injective i
  simpa using h

@[simp] theorem of_inv {i : LeftIndex} (x : LeftFactor G i) :
    CoprodI.of (M := LeftFactor G) (i := i) x⁻¹ =
      (CoprodI.of (M := LeftFactor G) (i := i) x)⁻¹ :=
  map_inv
    (CoprodI.of (M := LeftFactor G) (i := i) : LeftFactor G i →* LeftProduct G) x

@[simp] theorem old_inv (g : G) : old (g⁻¹) = (old g)⁻¹ :=
  of_inv (G := G) (i := LeftIndex.old) g

theorem freeGenerator_ne_one : FreeGroup.of () ≠ (1 : FreeGroup Unit) :=
  by simpa only [zpow_one] using
    FreeGroup.unitGenerator_zpow_ne_one 1 one_ne_zero

theorem beta_ne_one : (beta : LeftProduct G) ≠ 1 := by
  apply of_ne_one
  exact freeGenerator_ne_one

/-- The component maps retaining the `beta` factor and killing the other factors. -/
def leftFactorToBeta : ∀ i : LeftIndex, LeftFactor G i →* FreeGroup Unit
  | .old => 1
  | .alpha => 1
  | .beta => MonoidHom.id _

/-- The projection onto the `beta` cyclic factor. -/
def betaProjection : LeftProduct G →* FreeGroup Unit :=
  CoprodI.lift leftFactorToBeta

@[simp] theorem betaProjection_old (g : G) : betaProjection (old g) = 1 := by
  exact CoprodI.lift_of leftFactorToBeta (i := LeftIndex.old) g

@[simp] theorem betaProjection_beta :
    betaProjection (beta : LeftProduct G) = FreeGroup.of () := by
  exact CoprodI.lift_of leftFactorToBeta (i := LeftIndex.beta) (FreeGroup.of ())

theorem beta_zpow_ne_one (k : ℤ) (hk : k ≠ 0) :
    (beta : LeftProduct G) ^ k ≠ 1 := by
  intro h
  apply FreeGroup.unitGenerator_zpow_ne_one k hk
  simpa using congrArg betaProjection h

theorem old_mul_beta_ne_one (z : G) :
    old z * beta ≠ (1 : LeftProduct G) := by
  intro h
  apply freeGenerator_ne_one
  simpa using congrArg betaProjection h

theorem beta_mul_old_mul_beta_ne_one (z : G) :
    beta * (old z * beta) ≠ (1 : LeftProduct G) := by
  intro h
  apply FreeGroup.unitGenerator_zpow_ne_one 2 (by norm_num)
  calc
    (FreeGroup.of () : FreeGroup Unit) ^ (2 : ℤ) =
        FreeGroup.of () * FreeGroup.of () := zpow_two _
    _ = 1 := by simpa using congrArg betaProjection h

theorem inv_old_mul_beta_inv_mul_beta_inv_ne_one (z : G) :
    (old z * beta)⁻¹ * beta⁻¹ ≠ (1 : LeftProduct G) := by
  intro h
  apply FreeGroup.unitGenerator_zpow_ne_one (-2) (by norm_num)
  calc
    (FreeGroup.of () : FreeGroup Unit) ^ (-2 : ℤ) =
        (FreeGroup.of ())⁻¹ * (FreeGroup.of ())⁻¹ := by
          simp [zpow_neg, pow_two]
    _ = 1 := by simpa using congrArg betaProjection h

/-! The inner commutator is cyclically reduced of free-product length four. -/

/-- The nonempty reduced word representing the distinguished commutator. -/
def commutatorWord (w : G) (hw : w ≠ 1) :
    CoprodI.NeWord (LeftFactor G) LeftIndex.old LeftIndex.beta :=
  .append
    (.singleton (i := LeftIndex.old) w⁻¹ (inv_ne_one.mpr hw)) (by decide)
    (.append
      (.singleton (i := LeftIndex.beta) (FreeGroup.of ())⁻¹
        (inv_ne_one.mpr freeGenerator_ne_one)) (by decide)
      (.append
        (.singleton (i := LeftIndex.old) w hw) (by decide)
        (.singleton (i := LeftIndex.beta) (FreeGroup.of ()) freeGenerator_ne_one)))

@[simp] theorem commutatorWord_prod (w : G) (hw : w ≠ 1) :
    (commutatorWord w hw).prod = (old w)⁻¹ * beta⁻¹ * old w * beta := by
  simp only [commutatorWord, CoprodI.NeWord.append_prod,
    CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.old),
    CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.beta),
    of_inv (G := G) (i := LeftIndex.old) w,
    of_inv (G := G) (i := LeftIndex.beta) (FreeGroup.of ()), old, beta]
  rw [CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.old) w hw,
    CoprodI.NeWord.prod_singleton (M := LeftFactor G) (i := LeftIndex.beta)
      (FreeGroup.of ()) freeGenerator_ne_one]
  simp only [mul_assoc]

/-!
Powers of a cyclically reduced nonempty free-product word are nonempty.
This is the first reusable normal-form lemma needed for `L₃`.
-/

/-- The reduced word representing a positive power of a cyclically reduced word. -/
def positivePowerWord {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) :
    (k : ℕ) → CoprodI.NeWord (LeftFactor G) i j
  | 0 => u
  | k + 1 => .append (positivePowerWord u hij k) hij u

@[simp] theorem positivePowerWord_prod {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (k : ℕ) :
    (positivePowerWord u hij k).prod = u.prod ^ (k + 1) := by
  induction k with
  | zero => simp [positivePowerWord]
  | succ k ih =>
      calc
        (positivePowerWord u hij (k + 1)).prod =
            (positivePowerWord u hij k).prod * u.prod := by
              simp only [positivePowerWord, CoprodI.NeWord.append_prod]
        _ = u.prod ^ (k + 1) * u.prod := by rw [ih]
        _ = u.prod ^ (k + 1 + 1) := (pow_succ _ _).symm

theorem positivePowerWord_prod_ne_one {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i) (k : ℕ) :
    u.prod ^ (k + 1) ≠ 1 := by
  rw [← positivePowerWord_prod u hij]
  intro h
  classical
  have hnormal :
      CoprodI.Word.equiv (M := LeftFactor G) (positivePowerWord u hij k).prod =
        (positivePowerWord u hij k).toWord := by
    change (CoprodI.Word.equiv (M := LeftFactor G))
        ((CoprodI.Word.equiv (M := LeftFactor G)).symm
          (positivePowerWord u hij k).toWord) = _
    exact (CoprodI.Word.equiv (M := LeftFactor G)).apply_symm_apply _
  rw [h] at hnormal
  have hword : (positivePowerWord u hij k).toWord =
      (CoprodI.Word.empty : CoprodI.Word (LeftFactor G)) := by
    simpa [CoprodI.Word.equiv] using hnormal.symm
  exact (CoprodI.NeWord.toList_ne_nil (positivePowerWord u hij k))
    (by simpa [CoprodI.NeWord.toWord] using congrArg CoprodI.Word.toList hword)

theorem zpow_ne_one_of_cyclicallyReduced {i j : LeftIndex}
    (u : CoprodI.NeWord (LeftFactor G) i j) (hij : j ≠ i)
    (k : ℤ) (hk : k ≠ 0) : u.prod ^ k ≠ 1 := by
  cases k with
  | ofNat k =>
      cases k with
      | zero => exact (hk rfl).elim
      | succ k =>
          simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
            positivePowerWord_prod_ne_one u hij k
  | negSucc k =>
      simpa only [zpow_negSucc] using
        inv_ne_one.mpr (positivePowerWord_prod_ne_one u hij k)

theorem commutator_zpow_ne_one (w : G) (hw : w ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    ((old w)⁻¹ * beta⁻¹ * old w * beta) ^ k ≠ 1 := by
  rw [← commutatorWord_prod w hw]
  exact zpow_ne_one_of_cyclicallyReduced (commutatorWord w hw) (by decide) k hk

/-! A nested two-factor presentation is convenient for the outer alpha
normal-form calculation.  `LeftProduct G` is used as the base factor; its
extra unused free generator is harmless. -/

/-- The labels of the base factor and the outer conjugating cyclic factor. -/
inductive OuterIndex
  | base
  | alpha
  deriving DecidableEq

/-- The group corresponding to the base or outer cyclic factor. -/
def OuterFactor (G : Type) [Group G] : OuterIndex → Type
  | .base => LeftProduct G
  | .alpha => FreeGroup Unit

@[reducible] instance outerFactorGroup : ∀ i, Group (OuterFactor G i) := fun i => by
  cases i <;> simp only [OuterFactor] <;> infer_instance

/-- The outer free product separating the conjugating generator from the base group. -/
abbrev MillerLeft (G : Type) [Group G] := CoprodI (OuterFactor G)

/-- The inclusion of the base free product into the outer free product. -/
def baseOf (x : LeftProduct G) : MillerLeft G :=
  CoprodI.of (i := OuterIndex.base) x

/-- The generator of the outer cyclic factor. -/
def outerAlpha : MillerLeft G :=
  CoprodI.of (i := OuterIndex.alpha) (FreeGroup.of ())

@[simp] theorem baseOf_inv (x : LeftProduct G) : baseOf x⁻¹ = (baseOf x)⁻¹ :=
  map_inv
    (CoprodI.of (M := OuterFactor G) (i := OuterIndex.base) :
      LeftProduct G →* MillerLeft G) x

@[simp] theorem baseOf_zpow (x : LeftProduct G) (k : ℤ) :
    baseOf (x ^ k) = baseOf x ^ k :=
  map_zpow _ _ _

/-- The five proposed left-hand amalgamating generators in the outer free product. -/
def outerLeftBasis (w z : G) : Fin 5 → MillerLeft G
  | 0 => baseOf beta
  | 1 => outerAlpha⁻¹ * baseOf beta * outerAlpha
  | 2 => (outerAlpha ^ 2)⁻¹ * (baseOf beta)⁻¹ * outerAlpha *
      baseOf beta * outerAlpha ^ 2
  | 3 => (outerAlpha ^ 3)⁻¹ *
      baseOf ((old w)⁻¹ * beta⁻¹ * old w * beta) * outerAlpha ^ 3
  | 4 => (outerAlpha ^ 2)⁻¹ * baseOf (old z * beta) * outerAlpha ^ 4

/-- The one-letter reduced word for a nonidentity base-group element. -/
def baseSingleton (x : LeftProduct G) (hx : x ≠ 1) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.base OuterIndex.base :=
  .singleton x hx

/-- The one-letter reduced word in the `alpha` factor. -/
def alphaSingleton (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .singleton ((FreeGroup.of () : FreeGroup Unit) ^ k)
    (FreeGroup.unitGenerator_zpow_ne_one k hk)

@[simp] theorem baseSingleton_prod (x : LeftProduct G) (hx : x ≠ 1) :
    (baseSingleton x hx).prod = baseOf x := by
  exact CoprodI.NeWord.prod_singleton (M := OuterFactor G) (i := OuterIndex.base) x hx

@[simp] theorem alphaSingleton_prod (k : ℤ) (hk : k ≠ 0) :
    (alphaSingleton (G := G) k hk).prod = outerAlpha ^ k := by
  change (CoprodI.of (M := OuterFactor G) (i := OuterIndex.alpha))
      ((FreeGroup.of ()) ^ k) =
    ((CoprodI.of (M := OuterFactor G) (i := OuterIndex.alpha))
      (FreeGroup.of ())) ^ k
  exact map_zpow _ _ _

/-- The reduced block representing a power of the first conjugated left generator. -/
def leftPowerWord1 (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-1) (by norm_num)) (by decide)
    (.append (baseSingleton (beta ^ k) (beta_zpow_ne_one k hk)) (by decide)
      (alphaSingleton 1 (by norm_num)))

/-- The reduced block representing a power of the second conjugated left generator. -/
def leftPowerWord2 (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-2) (by norm_num)) (by decide)
    (.append (baseSingleton beta⁻¹ (inv_ne_one.mpr beta_ne_one)) (by decide)
      (.append (alphaSingleton k hk) (by decide)
        (.append (baseSingleton beta beta_ne_one) (by decide)
          (alphaSingleton 2 (by norm_num)))))

/-- The reduced block representing a power of the commutator-conjugated left generator. -/
def leftPowerWord3 (w : G) (hw : w ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    CoprodI.NeWord (OuterFactor G) OuterIndex.alpha OuterIndex.alpha :=
  .append (alphaSingleton (-3) (by norm_num)) (by decide)
    (.append
      (baseSingleton (((old w)⁻¹ * beta⁻¹ * old w * beta) ^ k)
        (commutator_zpow_ne_one w hw k hk)) (by decide)
      (alphaSingleton 3 (by norm_num)))

theorem leftPowerWord1_prod (w z : G) (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord1 (G := G) k hk).prod = outerLeftBasis w z 1 ^ k := by
  simp only [leftPowerWord1, Int.reduceNeg, CoprodI.NeWord.append_prod, alphaSingleton_prod,
    zpow_neg, zpow_ofNat, pow_one, baseSingleton_prod, baseOf_zpow, outerLeftBasis]
  symm
  rw [show outerAlpha⁻¹ * baseOf beta * outerAlpha =
      outerAlpha⁻¹ * baseOf beta * (outerAlpha⁻¹)⁻¹ by group]
  rw [conj_zpow]
  group

theorem leftPowerWord2_prod (w z : G) (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord2 (G := G) k hk).prod = outerLeftBasis w z 2 ^ k := by
  simp only [leftPowerWord2, Int.reduceNeg, CoprodI.NeWord.append_prod, alphaSingleton_prod,
    zpow_neg, zpow_ofNat, baseSingleton_prod, baseOf_inv, outerLeftBasis]
  symm
  rw [show (outerAlpha ^ 2)⁻¹ * (baseOf beta)⁻¹ * outerAlpha *
        baseOf beta * outerAlpha ^ 2 =
      (outerAlpha ^ 2)⁻¹ *
        ((baseOf beta)⁻¹ * outerAlpha * ((baseOf beta)⁻¹)⁻¹) *
        (((outerAlpha ^ 2)⁻¹)⁻¹) by group]
  rw [conj_zpow, conj_zpow]
  group

theorem leftPowerWord3_prod (w z : G) (hw : w ≠ 1)
    (k : ℤ) (hk : k ≠ 0) :
    (leftPowerWord3 w hw k hk).prod = outerLeftBasis w z 3 ^ k := by
  simp only [leftPowerWord3, Int.reduceNeg, CoprodI.NeWord.append_prod, alphaSingleton_prod,
    zpow_neg, zpow_ofNat, baseSingleton_prod, baseOf_zpow, outerLeftBasis]
  symm
  rw [show (outerAlpha ^ 3)⁻¹ *
        baseOf ((old w)⁻¹ * beta⁻¹ * old w * beta) * outerAlpha ^ 3 =
      (outerAlpha ^ 3)⁻¹ *
        baseOf ((old w)⁻¹ * beta⁻¹ * old w * beta) *
        (((outerAlpha ^ 3)⁻¹)⁻¹) by group]
  rw [conj_zpow]
  group

end Undecidability.MillerTancer.LeftNormalForm
