/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Paper.Sec3
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Paper, §4: descent implies nil-purity

* Lemma 4.1 (`lem:ML`) is `isProZero_iff_lim` (`Towers/AddCommGrp.lean`).
* Theorem 4.2 (`thm:descent`): `IsDescentType.isNilPure`. With `W` the sum of the small model of
  the compact objects (`compactsSum`), `G_n = Hom(𝟙, I^{⊗ n} ⊗ W)` has `lim = 0` and, via
  `W^{(ℕ)}`, `lim¹ = 0` on `G^{(ℕ)}` (`limOneVanishes_sumTower`), so `G` is pro-zero; duality then
  makes `δ^{⊗ N}` phantom (`isPhantom_of_whiskerRight_compactsSum`). The paper picks `W` with
  `W ≅ W^{(ℕ)}`; we apply descent type to `W` and to `W^{(ℕ)}` instead.
* Proof of Theorem A (`thm:A`), (2) ⇒ (1): `IsEffectiveDescentType.isDescentType`. The other
  implications are Theorem 4.2, Theorem 3.6 and Lemma 2.7; `theoremA_of_splitMono` in
  `TheoremA.lean` assembles them.
* Remark 4.3 (`rem:unit-only`): Theorem A is stated for any `η` with `B ⊗ η` split
  (`theoremA_of_splitMono`); for arbitrary `η`, (1) ⇒ (3) ⇒ (4) ⇒ (2) still holds
  (`theoremA_chain_of_unitMap`), and `η = 0 : 𝟙 ⟶ 𝟙` shows that (4) ⇒ (3) can fail
  (`zeroUnit_counterexample`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated ZeroObject

universe v u

namespace RigidDescent

open Tower

/-- `lim¹ = 0` transfers along levelwise bijections that commute with the transition maps
`G_{m+1} → G_m`. -/
lemma LimOneVanishes.of_bijective {G G' : ℕᵒᵖ ⥤ AddCommGrpCat.{v}} (h : LimOneVanishes G')
    (φ : ∀ m, G.obj (op m) →+ G'.obj (op m)) (hφ : ∀ m, Function.Bijective (φ m))
    (hnat : ∀ m x, φ m (Tower.t G (Nat.le_succ m) x) =
      Tower.t G' (Nat.le_succ m) (φ (m + 1) x)) :
    LimOneVanishes G := by
  intro a
  obtain ⟨b', hb'⟩ := h fun m => φ m (a m)
  choose b hb using fun m => (hφ m).2 (b' m)
  refine ⟨b, fun m => (hφ m).1 ?_⟩
  rw [map_sub, hnat, hb, hb]
  exact hb' m

variable {T : Type u} [Category.{v} T]

/-! ### Transition maps of `I^{⊗ n} ⊗ X` -/

section TowerMaps

variable [MonoidalCategory T] {I : T} (δ : I ⟶ 𝟙_ T) (X : T)

lemma tensorPowTower_t_succ (n : ℕ) :
    Tower.t (tensorPowTower δ X) (Nat.le_succ n) =
      (δ ▷ tensorPow I n ≫ (λ_ (tensorPow I n)).hom) ▷ X :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The transition map `I^{⊗ n} ⊗ X ⟶ I^{⊗ 0} ⊗ X` is `δ^{⊗ n} ⊗ X`. -/
lemma tensorPowTower_t_zero (n : ℕ) :
    Tower.t (tensorPowTower δ X) (Nat.zero_le n) = tensorPowHom δ n ▷ X := by
  induction n with
  | zero => exact (Tower.t_refl _ 0).trans (id_whiskerRight _ _).symm
  | succ n ih =>
    have h := (Tower.t_comp (tensorPowTower δ X) (Nat.zero_le n) (Nat.le_succ n)).symm
    rw [tensorPowTower_t_succ, ih] at h
    refine h.trans ?_
    exact (comp_whiskerRight _ _ _).symm.trans
      (congrArg (fun f : tensorPow I (n + 1) ⟶ 𝟙_ T => f ▷ X) (tensorPowHom_succ δ n).symm)

end TowerMaps

/-! ### `Hom(K, Q ⊗ W^{(ℕ)}) ≅ Hom(K, Q ⊗ W)^{(ℕ)}` for compact `K` -/

variable [Preadditive T] [HasShift T ℤ]

/-- Countable coproducts exist in a compactly generated category. -/
instance CompactlyGenerated.hasCoproductsOfShape_nat [CompactlyGenerated T] :
    HasCoproductsOfShape ℕ T :=
  hasCoproductsOfShape_of_small.{v} T ℕ

section SumMap

variable [MonoidalCategory T] [CompactlyGenerated T] (K Q W : T)

/-- `⊕_ℕ Hom(K, Q ⊗ W) ⟶ Hom(K, Q ⊗ W^{(ℕ)})`, induced by the inclusions of the summands. -/
noncomputable def sumMap : (ℕ →₀ (K ⟶ Q ⊗ W)) →+ (K ⟶ Q ⊗ ∐ fun _ : ℕ => W) :=
  Finsupp.liftAddHom fun k => Preadditive.rightComp K (Q ◁ Sigma.ι (fun _ : ℕ => W) k)

lemma sumMap_single (k : ℕ) (x : K ⟶ Q ⊗ W) :
    sumMap K Q W (Finsupp.single k x) = x ≫ Q ◁ Sigma.ι (fun _ : ℕ => W) k :=
  Finsupp.liftAddHom_apply_single _ _ _

lemma sumMap_apply (f : ℕ →₀ (K ⟶ Q ⊗ W)) :
    sumMap K Q W f = ∑ k ∈ f.support, f k ≫ Q ◁ Sigma.ι (fun _ : ℕ => W) k :=
  Finsupp.liftAddHom_apply _ _

/-- `sumMap` is natural: maps `g : Q' ⊗ W ⟶ Q ⊗ W` and `g' : Q' ⊗ W^{(ℕ)} ⟶ Q ⊗ W^{(ℕ)}`
compatible with the inclusions of the summands commute with it. -/
lemma sumMap_comp {Q Q' : T} (g : Q' ⊗ W ⟶ Q ⊗ W)
    (g' : Q' ⊗ (∐ fun _ : ℕ => W) ⟶ Q ⊗ ∐ fun _ : ℕ => W)
    (hg : ∀ k, Q' ◁ Sigma.ι (fun _ : ℕ => W) k ≫ g' = g ≫ Q ◁ Sigma.ι (fun _ : ℕ => W) k)
    (f : ℕ →₀ (K ⟶ Q' ⊗ W)) :
    sumMap K Q W (Finsupp.mapRange.addMonoidHom (Preadditive.rightComp K g) f) =
      sumMap K Q' W f ≫ g' := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, hf, hf', Preadditive.add_comp]
  | single k x =>
    rw [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
    change sumMap K Q W (Finsupp.single k (x ≫ g)) = _
    rw [sumMap_single, sumMap_single, Category.assoc, Category.assoc, hg]

variable [MonoidalClosed T]

/-- `Q ⊗ W^{(ℕ)} ≅ (Q ⊗ W)^{(ℕ)}`, as `Q ⊗ -` is a left adjoint. -/
noncomputable abbrev sumTensorIso : Q ⊗ (∐ fun _ : ℕ => W) ≅ ∐ fun _ : ℕ => Q ⊗ W :=
  PreservesCoproduct.iso (tensorLeft Q) fun _ : ℕ => W

@[reassoc]
lemma whiskerLeft_ι_sumTensorIso_hom (k : ℕ) :
    Q ◁ Sigma.ι (fun _ : ℕ => W) k ≫ (sumTensorIso Q W).hom =
      Sigma.ι (fun _ : ℕ => Q ⊗ W) k := by
  have h : Sigma.ι (fun _ : ℕ => Q ⊗ W) k ≫ (sumTensorIso Q W).inv =
      Q ◁ Sigma.ι (fun _ : ℕ => W) k := by
    rw [PreservesCoproduct.inv_hom]
    exact ι_comp_sigmaComparison (tensorLeft Q) (fun _ : ℕ => W) k
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma sumMap_comp_hom (f : ℕ →₀ (K ⟶ Q ⊗ W)) :
    sumMap K Q W f ≫ (sumTensorIso Q W).hom =
      ∑ k ∈ f.support, f k ≫ Sigma.ι (fun _ : ℕ => Q ⊗ W) k := by
  rw [sumMap_apply, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Category.assoc, whiskerLeft_ι_sumTensorIso_hom]

/-- For compact `K`, `⊕_ℕ Hom(K, Q ⊗ W) ⟶ Hom(K, Q ⊗ W^{(ℕ)})` is bijective, as `⊗` preserves
coproducts (paper, proof of Theorem 4.2). -/
lemma sumMap_bijective {K : T} (hK : IsCompactObj K) : Function.Bijective (sumMap K Q W) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).2 fun f hf => ?_, fun x => ?_⟩
  · ext k
    have h : (sumMap K Q W f ≫ (sumTensorIso Q W).hom) ≫
        Sigma.π (fun _ : ℕ => Q ⊗ W) k = 0 := by
      rw [hf, zero_comp, zero_comp]
    rw [sumMap_comp_hom, sum_comp_sigmaπ] at h
    rw [Finsupp.zero_apply]
    by_cases hk : k ∈ f.support
    · simpa [hk] using h
    · exact Finsupp.notMem_support_iff.1 hk
  · obtain ⟨F, a, ha⟩ := hK.isFiniteSum_of_small (x ≫ (sumTensorIso Q W).hom)
    refine ⟨∑ k ∈ F, Finsupp.single k (a k), ?_⟩
    rw [map_sum]
    simp only [sumMap_single]
    rw [← cancel_mono (sumTensorIso Q W).hom, ha, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Category.assoc, whiskerLeft_ι_sumTensorIso_hom]

variable {I : T} (δ : I ⟶ 𝟙_ T)

/-- Paper, proof of Theorem 4.2: for compact `K`, if `lim¹` vanishes on
`Hom(K, I^{⊗ n} ⊗ W^{(ℕ)})`, it vanishes on the countable sum of copies of
`Hom(K, I^{⊗ n} ⊗ W)`. -/
lemma limOneVanishes_sumTower {K : T} (hK : IsCompactObj K)
    (h : LimOneVanishes (tensorPowTower δ (∐ fun _ : ℕ => W) ⋙ preadditiveCoyoneda.obj (op K))) :
    LimOneVanishes (sumTower (tensorPowTower δ W ⋙ preadditiveCoyoneda.obj (op K))) :=
  LimOneVanishes.of_bijective h (fun m => sumMap K (tensorPow I m) W)
    (fun m => sumMap_bijective (tensorPow I m) W hK) fun m y =>
      sumMap_comp K W (Tower.t (tensorPowTower δ W) (Nat.le_succ m))
        (Tower.t (tensorPowTower δ (∐ fun _ : ℕ => W)) (Nat.le_succ m)) (fun k => by
        rw [tensorPowTower_t_succ, tensorPowTower_t_succ]
        exact whisker_exchange _ _) y

end SumMap

variable [HasZeroObject T] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-! ### The sum of the compact objects -/

section CompactsSum

variable [IsTriangulated T] [CompactlyGenerated T]

variable (T) in
/-- The sum of the small model of the compact objects: every compact object is a retract of
it. -/
noncomputable def compactsSum : T := ∐ compactObj T

lemma exists_retract_compactsSum {K : T} (hK : IsCompactObj K) :
    ∃ (s : K ⟶ compactsSum T) (r : compactsSum T ⟶ K), s ≫ r = 𝟙 K := by
  classical
  obtain ⟨i, ⟨e⟩⟩ := exists_iso_compactObj hK
  exact ⟨e.hom ≫ Sigma.ι _ i, Sigma.π _ i ≫ e.inv, by simp [compactsSum]⟩

end CompactsSum

variable [MonoidalCategory T]

/-! ### Theorem 4.2 -/

section Descent

variable [IsTriangulated T] [BraidedCategory T] [MonoidalClosed T] [TensorTriangulated T]
  [RigidlyCompactlyGenerated T]

omit [MonoidalClosed T] in
/-- Paper, proof of Theorem 4.2: if `Hom(𝟙, φ ⊗ W) = 0` for the sum `W` of the compact objects,
then `φ` is phantom. For compact `K`, `Hom(K, φ) ≅ Hom(𝟙, φ ⊗ DK)` as `K` is dualizable, and
the dual `DK` is compact, hence a retract of `W`. -/
lemma isPhantom_of_whiskerRight_compactsSum {Z Z' : T} (φ : Z ⟶ Z')
    (h : ∀ x : 𝟙_ T ⟶ Z ⊗ compactsSum T, x ≫ φ ▷ compactsSum T = 0) : IsPhantom φ := by
  intro K hK k
  obtain ⟨D, ⟨hD⟩⟩ := (RigidlyCompactlyGenerated.isCompactObj_iff_isDualizable K).1 hK
  have hDc : IsCompactObj D :=
    (RigidlyCompactlyGenerated.isCompactObj_iff_isDualizable D).2
      ⟨K, ⟨BraidedCategory.exactPairing_swap K D⟩⟩
  obtain ⟨s, r, hsr⟩ := exists_retract_compactsSum hDc
  have e : φ ▷ D = Z ◁ s ≫ φ ▷ compactsSum T ≫ Z' ◁ r := by
    rw [← whisker_exchange, ← MonoidalCategory.whiskerLeft_comp_assoc, hsr,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have h0 : η_ K D ≫ (k ≫ φ) ▷ D = 0 := by
    rw [comp_whiskerRight, e]
    simp only [← Category.assoc]
    rw [h, zero_comp]
  have h1 := tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight (Y' := D) (k ≫ φ)
  rw [h0] at h1
  have h2 : (λ_ K).hom ≫ k ≫ φ = 0 := by
    rw [← h1]
    simp [tensorRightHomEquiv]
  exact (cancel_epi (λ_ K).hom).1 (h2.trans comp_zero.symm)

/-- Paper, Theorem 4.2 (`thm:descent`): if `B` is of descent type, then `B` is nil-pure. -/
theorem IsDescentType.isNilPure {I : T} {δ : I ⟶ 𝟙_ T} (h : IsDescentType δ) :
    IsNilPure δ := by
  let W := compactsSum T
  let G := tensorPowTower δ W ⋙ preadditiveCoyoneda.obj (op (𝟙_ T))
  have hW := isHolim_zero_iff.1 (h W)
  have hX := isHolim_zero_iff.1 (h (∐ fun _ : ℕ => W))
  have h0 : LimVanishes G := limVanishes_of_isIso (𝟙_ T)
  have h1 : LimOneVanishes (sumTower G) :=
    limOneVanishes_sumTower W δ isCompactObj_unit (limOneVanishes_of_isIso (𝟙_ T))
  obtain ⟨N, hN0, hN⟩ :=
    isProZero_of_mittagLeffler (mittagLeffler_of_limOneVanishes_sumTower h1) h0 0
  refine ⟨N, isPhantom_of_whiskerRight_compactsSum _ fun x => ?_⟩
  have := ConcreteCategory.congr_hom hN x
  rw [← tensorPowTower_t_zero]
  exact this

/-! ### Theorem A, (2) ⇒ (1) -/

omit [IsTriangulated T] [BraidedCategory T] [MonoidalClosed T] [RigidlyCompactlyGenerated T] in
lemma whiskerLeft_whiskerRight_eq_zero {M X Y : T} {f : X ⟶ Y} (h : M ◁ f = 0) (Z : T) :
    M ◁ f ▷ Z = 0 := by
  rw [← cancel_mono (α_ M Y Z).inv, associator_inv_naturality_middle, h,
    MonoidalPreadditive.zero_whiskerRight, comp_zero, zero_comp]

omit [IsTriangulated T] [BraidedCategory T] [MonoidalClosed T] [RigidlyCompactlyGenerated T] in
/-- If `B ⊗ δ = 0`, the tower `B ⊗ I^{⊗ n} ⊗ X` has zero transition maps. -/
lemma whiskerLeft_tensorPowTower_t_succ_eq_zero {B I : T} {δ : I ⟶ 𝟙_ T} (hδ : B ◁ δ = 0)
    (X : T) (m : ℕ) : B ◁ Tower.t (tensorPowTower δ X) (Nat.le_succ m) = 0 := by
  have h : B ◁ ((δ ▷ tensorPow I m ≫ (λ_ (tensorPow I m)).hom) ▷ X) = 0 := by
    rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
      whiskerLeft_whiskerRight_eq_zero (whiskerLeft_whiskerRight_eq_zero hδ _) _, zero_comp]
  rw [tensorPowTower_t_succ]
  exact h

variable {B I : T} {η : 𝟙_ T ⟶ B} {δ : I ⟶ 𝟙_ T} {ε : B ⟶ I⟦(1 : ℤ)⟧}

omit [IsTriangulated T] [BraidedCategory T] [MonoidalClosed T] [RigidlyCompactlyGenerated T] in
/-- Paper, proof of Theorem A (`thm:A`), (2) ⇒ (1): as `B ⊗ η` is split, `B ⊗ δ = 0`, so the
tower `B ⊗ I^{⊗ n} ⊗ X` has zero transition maps; it is pro-zero with homotopy limit `0`. If
`B` is of effective descent type, `B ⊗ holim_n (I^{⊗ n} ⊗ X) = 0`, hence
`holim_n (I^{⊗ n} ⊗ X) = 0`. (This holds in any tensor-triangulated category with countable
products.) -/
theorem IsEffectiveDescentType.isDescentType [HasCountableProducts T]
    (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)]
    (hB : IsEffectiveDescentType B) : IsDescentType δ := by
  intro X
  have hδ : B ◁ δ = 0 := isTensorZero_δ hT
  have ht : ∀ m, Tower.t (tensorPowTower δ X ⋙ tensorLeft B) (Nat.le_succ m) = 0 := fun m =>
    whiskerLeft_tensorPowTower_t_succ_eq_zero hδ X m
  have hY0 : IsHolim (tensorPowTower δ X ⋙ tensorLeft B) 0 0 := isHolim_zero_of_t_eq_zero ht
  have hpc : IsProConstant (tensorPowTower δ X ⋙ tensorLeft B) :=
    IsProZero.isProConstant fun m => ⟨m + 1, Nat.le_succ m, ht m⟩
  obtain ⟨L, p, hL⟩ := exists_isHolim (tensorPowTower δ X)
  obtain ⟨φ, -⟩ := (hB.2 _ hpc L p hL).exists_iso hY0
  have hL0 : IsZero L := hB.1 L ((isZero_zero T).of_iso φ)
  have e : (fun m => hL0.isoZero.symm.hom ≫ p m) = 0 :=
    funext fun m => (isZero_zero T).eq_of_src _ _
  have := hL.of_iso hL0.isoZero.symm
  rwa [e] at this

/-! ### Remark 4.3 -/

omit [Preadditive T] [HasShift T ℤ] [HasZeroObject T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [IsTriangulated T] [BraidedCategory T] [MonoidalClosed T]
  [TensorTriangulated T] [RigidlyCompactlyGenerated T] in
/-- If `δ` is a split epimorphism, so is every `δ^{⊗ n}`. -/
lemma exists_comp_tensorPowHom_eq_id {I : T} {δ : I ⟶ 𝟙_ T} {g : 𝟙_ T ⟶ I}
    (hg : g ≫ δ = 𝟙 _) (n : ℕ) : ∃ s : 𝟙_ T ⟶ tensorPow I n, s ≫ tensorPowHom δ n = 𝟙 _ := by
  induction n with
  | zero => exact ⟨𝟙 _, Category.comp_id _⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨(λ_ (𝟙_ T)).inv ≫ (g ⊗ₘ s), ?_⟩
    change ((λ_ (𝟙_ T)).inv ≫ (g ⊗ₘ s)) ≫ (δ ⊗ₘ tensorPowHom δ n) ≫ (λ_ (𝟙_ T)).hom = 𝟙 _
    rw [Category.assoc, ← Category.assoc (g ⊗ₘ s), tensorHom_comp_tensorHom, hg, hs]
    simp

/-- Paper, Remark 4.3 (`rem:unit-only`): for an arbitrary map `η : 𝟙 ⟶ B`, with no condition on
`B ⊗ η`, the proofs still give (1) ⇒ (3) ⇒ (4) ⇒ (2) of Theorem A. -/
theorem theoremA_chain_of_unitMap (hT : Triangle.mk δ η ε ∈ distTriang T) :
    (IsDescentType δ → IsNilPure δ) ∧
      (IsNilPure δ → ∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal B E) ∧
      ((∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal B E) →
        IsEffectiveDescentType B) :=
  ⟨IsDescentType.isNilPure, fun h => h.exists_isPureMono hT,
    fun ⟨_, _, hj, hE⟩ => isEffectiveDescentType_of_isPureMono hj hE⟩

/-- Paper, Remark 4.3 (`rem:unit-only`): for `η = 0 : 𝟙 ⟶ 𝟙` and `T ≠ 0`, conditions (2) and
(4) of Theorem A hold and (3) fails, as `δ` is a split epimorphism. -/
theorem zeroUnit_counterexample {I : T} {δ : I ⟶ 𝟙_ T} {ε : 𝟙_ T ⟶ I⟦(1 : ℤ)⟧}
    (hT : Triangle.mk δ (0 : 𝟙_ T ⟶ 𝟙_ T) ε ∈ distTriang T) (hT0 : ∃ X : T, ¬ IsZero X) :
    IsEffectiveDescentType (𝟙_ T) ∧
      (∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal (𝟙_ T) E) ∧
      ¬ IsNilPure δ := by
  have h4 : ∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal (𝟙_ T) E :=
    ⟨𝟙_ T, 𝟙 _, isPureMono_of_isIso _, fun _ _ h => h⟩
  refine ⟨(theoremA_chain_of_unitMap hT).2.2 h4, h4, ?_⟩
  rintro ⟨n, hn⟩
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT (𝟙 (𝟙_ T)) (by simp)
  obtain ⟨s, hs⟩ := exists_comp_tensorPowHom_eq_id hg.symm n
  have h1 : IsZero (𝟙_ T) := by
    rw [IsZero.iff_id_eq_zero, ← hs]
    exact hn _ isCompactObj_unit s
  obtain ⟨X, hX⟩ := hT0
  exact hX ((Functor.map_isZero (tensorRight X) h1).of_iso (λ_ X).symm)

end Descent

end RigidDescent
