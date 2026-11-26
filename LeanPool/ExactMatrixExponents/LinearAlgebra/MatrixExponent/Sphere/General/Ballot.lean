/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Price

/-! # Indexing selectors on occupied occurrences -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse
open Coloring Finset Transcript

variable {J I : Type} {m h k : ℕ} (loc : J ↪ B m × B h) (pad : B k)

open scoped Classical in
/-- The condition `∀ v ∉ Set.range loc, c v.1 v.2 = pad` on the specified data. -/
def Supported (c : B m → B h → B k) : Prop :=
  ∀ v ∉ Set.range loc, c v.1 v.2 = pad

open scoped Classical in
/-- Extends the specified values along the indexing map, using a default elsewhere. -/
def pack (c : J → B k) (i : B m) (j : B h) :=
  Function.extend loc c (fun _ => pad) (i, j)

open scoped Classical in
/-- Computes the sample by the application `c (loc j).1 (loc j).2`. -/
def sample (c : B m → B h → B k) (j : J) := c (loc j).1 (loc j).2

open scoped Classical in
@[simp] theorem sample_pack (c : J → B k) : sample loc (pack loc pad c) = c :=
  funext fun j => loc.injective.extend_apply c (fun _ => pad) j

open scoped Classical in
theorem pack_supported (c : J → B k) : Supported loc pad (pack loc pad c) :=
  fun _ hv => Function.extend_apply' _ _ _ hv

open scoped Classical in
theorem pack_sample {c : B m → B h → B k} (hc : Supported loc pad c) :
    pack loc pad (sample loc c) = c := by
  have he (v : B m × B h) : pack loc pad (sample loc c) v.1 v.2 = c v.1 v.2 := by
    by_cases hv : v ∈ Set.range loc
    · obtain ⟨i, rfl⟩ := hv
      exact congrFun (sample_pack loc pad (sample loc c)) i
    · rw [pack_supported loc pad _ v hv, hc v hv]
  exact funext fun i => funext fun j => he (i, j)

open scoped Classical in
/-- Compression preserves the unique code of every supported branch. -/
def compress (s : Selector I (B m → B h → B k))
    (ok : ∀ i, Supported loc pad (s.write i)) : Selector I (J → B k) where
  write i := sample loc (s.write i)
  read x := s.read (pack loc pad x)
  valid x i := by
    rw [s.valid]
    exact ⟨fun e => (sample_pack loc pad x).symm.trans (congrArg (sample loc) e),
      fun e => e ▸ pack_sample loc pad (ok i)⟩

open scoped Classical in
theorem of_weight {F : Type} [Zero F] (s : Selector I (B m → B h → B k))
    (ok : ∀ i, Supported loc pad (s.write i)) {w : I → F} {c : B m → B h → B k}
    (hc : (s.read c).elim 0 w ≠ 0) : Supported loc pad c := by
  cases e : s.read c with
  | none => simp [e] at hc
  | some i => rw [(s.valid c i).mp e]; exact ok i

variable [Fintype J]

open scoped Classical in
theorem card_le [Fintype I] (s : Selector I (J → B k)) :
    Fintype.card I ≤ 2 ^ (k * Fintype.card J) := by
  have h := Fintype.card_le_of_injective s.write s.injective
  simpa only [Fintype.card_fun, Fintype.card_fin, pow_mul] using h

open scoped Classical in
/-- Padded occurrences do not count toward the number of choices. -/
theorem sum_pack {F : Type} [CommSemiring F] (weight f : (B m → B h → B k) → F)
    (support : ∀ c, weight c ≠ 0 → Supported loc pad c) :
    (∑ c, weight c * f c) = ∑ x, weight (pack loc pad x) * f (pack loc pad x) := by
  have inj : Function.Injective (pack loc pad) :=
    Function.LeftInverse.injective (sample_pack loc pad)
  let active := univ.image (pack loc pad)
  calc
    _ = ∑ c ∈ active, weight c * f c := (sum_subset (subset_univ _) (by
      intro c _ hc
      have hw : weight c = 0 := by
        by_contra h
        exact hc (mem_image.mpr ⟨sample loc c, mem_univ _, pack_sample loc pad (support c h)⟩)
      rw [hw, zero_mul])).symm
    _ = _ := sum_image inj.injOn

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse
end

/- # The unique ballot at a vacant occurrence -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Finset

variable {F K N : Type} {m d h e M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h e M r t q D k n u j z)

open scoped Classical in
/-- The ordinal coding the ballot whose digits are all zero. -/
def pad : B U.digits := U.ballot (fun _ _ => 0)

variable [Field F] (data : U.rows.obj) (c : U.selectors.obj)

open scoped Classical in
theorem score_away (hn : U.score data c ≠ 0) (v : B m × B h)
    (hv : U.menu ((data v.1).2 v.2) = none) : c v.1 v.2 = U.pad := by
  let w := U.view (((U.around data c) v.1).2 v.2)
  have he : w 0 0 = (none, U.ballot.symm (c v.1 v.2)) := by
    simp only [w, view, around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin, hv]
  have hw : w.valid U.positive := by
    by_contra ho
    apply hn
    unfold score Fmt.weight
    apply prod_eq_zero (mem_univ v.1)
    apply prod_eq_zero (mem_univ v.2)
    exact ite_eq_right ho
  apply U.ballot.symm.injective
  rw [pad, U.ballot.symm_apply_apply]
  funext i j
  have hz : tally (U.ballot.symm (c v.1 v.2) i) = 0 := by
    simpa [Lens.ask, he, quota] using hw i
  have le : (U.ballot.symm (c v.1 v.2) i j).val ≤ tally (U.ballot.symm (c v.1 v.2) i) :=
    single_le_sum (fun l _ => Nat.zero_le (U.ballot.symm (c v.1 v.2) i l).val) (mem_univ j)
  exact Fin.ext (Nat.eq_zero_of_le_zero (le.trans_eq hz))

open scoped Classical in
theorem supported {J : Type} (loc : J ↪ B m × B h)
    (vacant : ∀ v ∉ Set.range loc, U.menu ((data v.1).2 v.2) = none)
    (hn : U.score data c ≠ 0) : Sparse.Supported loc U.pad c :=
  fun v h => U.score_away data c hn v (vacant v h)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
end

/- # Reading a whole motion history from its selector words -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local
open Assembly Coloring

namespace Design

variable (a : Design) {e k : ℕ} (start : (a.port e).obj)

/-- The metadata tape, computed independently of the weights. -/
def path : (i : ℕ) → (Fin i → (a.selectors k).obj) → (a.port (a.widthAt e k i)).obj
  | 0, _ => start
  | i + 1, c => a.update (path i (Fin.init c)) (c (Fin.last i))

theorem path_snoc {i : ℕ} (c : Fin i → (a.selectors k).obj) (t : (a.selectors k).obj) :
    a.path start (i + 1) (Fin.snoc c t) = a.update (a.path start i c) t := by
  rw [path, Fin.init_snoc, Fin.snoc_last]

variable {F N A : Type} [Field F] [Fintype F] [ExpChar F a.p]
  (hF : a.M * (2 * a.D + 1) < Fintype.card F) (menu : a.Menu F N A e)

/-- In the case `0, _, _`, this construction gives `1`. -/
def totalCharge : (i : ℕ) → i ≤ a.waves → (Fin i → (a.selectors k).obj) → F
  | 0, _, _ => 1
  | i + 1, hi, c =>
    let j : Fin a.waves := ⟨i, hi⟩
    let p := a.path start i (Fin.init c)
    totalCharge i j.isLt.le (Fin.init c) *
      Fmt.weight (a.tariff hF j (a.menuAt hF menu k i j.isLt.le) k) (a.around p (c (Fin.last i)))

theorem charge_snoc {i : ℕ} (hi : i < a.waves) (c : Fin i → (a.selectors k).obj)
    (t : (a.selectors k).obj) :
    a.totalCharge start hF menu (i + 1) hi (Fin.snoc c t) =
      a.totalCharge start hF menu i hi.le c *
        Fmt.weight (a.tariff hF ⟨i, hi⟩ (a.menuAt hF menu k i hi.le) k) (a.around (a.path start i
          c) t) := by
  rw [totalCharge, Fin.init_snoc, Fin.snoc_last]

end Design

namespace Scenario

variable {F N A : Type} [Field F] {x y : Wire} {a : Design} (w : Scenario F N A a x y)
  {k i : ℕ}

/-- The indexing data represented by `Fin i → w.V → B k`. -/
abbrev History (k i : ℕ) := Fin i → w.V → B k

/-- Evaluates `Sparse.pack w.atlas.coord 0 (c j)` at the input `j`. -/
def tapes (c : w.History k i) : Fin i → (a.selectors k).obj :=
  fun j => Sparse.pack w.atlas.coord 0 (c j)

theorem tapes_snoc (c : w.History k i) (t : w.V → B k) :
    w.tapes (Fin.snoc c t) = Fin.snoc (w.tapes c) (Sparse.pack w.atlas.coord 0 t) := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j <;> simp [tapes]

end Scenario
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local
end

/- # Factoring the charge of a history over its occupied cells -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse
open Coloring Finset

open scoped Classical in
theorem prod_occupied {V F : Type} [Fintype V] [CommMonoid F] {m h : ℕ}
    (loc : V ↪ B m × B h) (f : B m × B h → F) (off : ∀ x ∉ Set.range loc, f x = 1) :
    (∏ i, ∏ j, f (i, j)) = ∏ v, f (loc v) := by
  rw [← Fintype.prod_prod_type, ← prod_image loc.injective.injOn]
  symm
  apply prod_subset (subset_univ _)
  intro i _ hi
  exact off i (by simpa using hi)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Sparse

namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Design
open Assembly Coloring Finset

variable (a : Design) {e k : ℕ} {F N A : Type} [Field F] [Fintype F] [ExpChar F a.p]
  (start : (a.port e).obj) (hF : a.M * (2 * a.D + 1) < Fintype.card F) (menu : a.Menu F N A e)

open scoped Classical in
/-- In the case `0, _, _, _`, this construction gives `1`. -/
def localCharge : (i : ℕ) → i ≤ a.waves → (Fin i → (a.selectors k).obj) → B a.m × B a.h → F
  | 0, _, _, _ => 1
  | i + 1, hi, c, v =>
    let j : Fin a.waves := ⟨i, hi⟩
    let p := a.path start i (Fin.init c)
    localCharge i j.isLt.le (Fin.init c) v *
      a.tariff hF j (a.menuAt hF menu k i j.isLt.le) k (((a.around p (c (Fin.last i))) v.1).2 v.2)

open scoped Classical in
theorem total_eq_prod (i : ℕ) (hi : i ≤ a.waves) (c : Fin i → (a.selectors k).obj) :
    a.totalCharge start hF menu i hi c = ∏ v, ∏ w, a.localCharge start hF menu i hi c (v, w) := by
  induction i with
  | zero => simp [totalCharge, localCharge]
  | succ i ih =>
    simp only [totalCharge, localCharge, Fmt.weight, prod_mul_distrib]
    rw [ih]

open scoped Classical in
theorem vacant_step (j : Fin a.waves) (c : (a.selectors k).obj) (v : B a.m × B a.h)
    (hv : (menu ((start v.1).2 v.2)).2 = none) (hc : c v.1 v.2 = 0) :
    (a.nextMenu hF j menu k (((a.update start c) v.1).2 v.2)).2 = none ∧
      a.tariff hF j menu k (((a.around start c) v.1).2 v.2) = 1 := by
  have origin : ((a.around start c) v.1).2 v.2 0 0 = ((start v.1).2 v.2, 0) := by
    simp only [around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin, hc]
  simp [nextMenu, update, Fmt.update, tariff, route, charge, selected, origin, hv]

open scoped Classical in
theorem vacant_path (v : B a.m × B a.h) (hv : (menu ((start v.1).2 v.2)).2 = none)
    (i : ℕ) (hi : i ≤ a.waves) (c : Fin i → (a.selectors k).obj) (hc : ∀ j, c j v.1 v.2 = 0) :
    (a.menuAt hF menu k i hi (((a.path start i c) v.1).2 v.2)).2 = none ∧
      a.localCharge start hF menu i hi c v = 1 := by
  induction i with
  | zero => exact ⟨hv, rfl⟩
  | succ i ih =>
    obtain ⟨empty, unit⟩ := ih (Nat.le_of_succ_le hi) (Fin.init c) (fun j => hc j.castSucc)
    obtain ⟨hm, ht⟩ := a.vacant_step _ hF _ ⟨i, hi⟩ _ v empty (hc (Fin.last i))
    exact ⟨hm, by rw [localCharge, unit, ht, one_mul]⟩

open scoped Classical in
theorem total_occupied {V : Type} [Fintype V] (loc : V ↪ B a.m × B a.h)
    (hv : ∀ v ∉ Set.range loc, (menu ((start v.1).2 v.2)).2 = none)
    (i : ℕ) (hi : i ≤ a.waves) (c : Fin i → (a.selectors k).obj)
    (hc : ∀ j, Sparse.Supported loc 0 (c j)) :
    a.totalCharge start hF menu i hi c = ∏ v, a.localCharge start hF menu i hi c (loc v) := by
  rw [total_eq_prod]
  exact Sparse.prod_occupied loc _ (fun v h =>
    (a.vacant_path start hF menu v (hv v h) i hi c (fun j => hc j v h)).2)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Design
end

/- # Wave selectors vanish outside the occupied occurrences -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring Transcript

variable {F A N : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {e k : ℕ} {x y : Wire} {menu : a.Menu F N A e}
  (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (s : w.Code j.val menu)
  (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

theorem selector_away (i : Branch w hF j s) (v : B a.m × B a.h) (hv : v ∉ Set.range w.atlas.coord) :
    (w.selector hF j s hk).write i v.1 v.2 = 0 := by
  apply Selector.scatter_away
  rintro ⟨t, ht⟩
  exact hv ⟨_, ht⟩

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end
