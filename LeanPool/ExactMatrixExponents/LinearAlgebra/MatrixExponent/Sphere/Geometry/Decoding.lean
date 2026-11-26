/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Origin
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps

/-!
# Reading the geometry from a finite tag and length words

Each output width digit uses the tag and just one digit of each length.
Thus the cost is linear in the length of a word for fixed tag, station and
span alphabets. The digit convention is arbitrary.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Geometry.Blueprint
open Coloring

variable {T X Y : Type} {w d e k : ℕ}

open scoped Classical in
/-- The distinguished word holds the common internal width. -/
abbrev LengthKey (k : ℕ) := Option (B k × Bool)
open scoped Classical in
/-- Indexes the read in by the coordinates of `X ⊕ (LengthKey k × Fin b)`. -/
abbrev ReadIn (X : Type) (k b : ℕ) := X ⊕ (LengthKey k × Fin b)
open scoped Classical in
/-- Indexes the read out by the coordinates of `Y ⊕ (B w × B e × Fin b)`. -/
abbrev ReadOut (Y : Type) (w e b : ℕ) := Y ⊕ (B w × B e × Fin b)

open scoped Classical in
/-- In the case `none`, this construction gives `u`. -/
def lengths (u : ℕ) (size : Option (B k) → Bool → ℕ) : LengthKey k → ℕ
  | none => u
  | some (v, s) => size (some v) s

variable (emb : T ↪ (X → Bool)) (blue : T → Blueprint w d e k)
  (info : T → Y → Bool) (outer : Bool ↪ B e) (b : ℕ) (bit : ℕ → Fin b → Bool)

open scoped Classical in
/-- Chooses the operation for the left or right summand. -/
def readIn (t : T) (u : ℕ) (size : Option (B k) → Bool → ℕ) : ReadIn X k b → Bool :=
  Sum.elim (emb t) (fun h => bit (lengths u size h.1) h.2)

open scoped Classical in
/-- Chooses the operation for the left or right summand. -/
def readOut (t : T) (u : ℕ) (size : Option (B k) → Bool → ℕ) : ReadOut Y w e b → Bool :=
  Sum.elim (info t) (fun h => bit ((blue t h.1).width u outer size h.2.1) h.2.2)

open scoped Classical in
private def sliceCode : T × (LengthKey k → Bool) ↪ (X ⊕ LengthKey k → Bool) where
  toFun p := Sum.elim (emb p.1) p.2
  inj' _ _ h := Prod.ext (emb.injective (funext fun i => congrFun h (.inl i)))
    (funext fun i => congrFun h (.inr i))

open scoped Classical in
private def digit (v : B w) (s : B e) (j : Fin b) (t : T × (LengthKey k → Bool)) :=
  let o := blue t.1 v
  let side h := o.name.elim (bit 0 j) fun i => t.2 (some (i, h))
  if (o.peer s).isSome then t.2 none else
    if s = outer false then side false else if s = outer true then side true else bit 0 j

open scoped Classical in
private theorem digit_eq (v : B w) (s : B e) (j : Fin b)
    (t : T) (u : ℕ) (size : Option (B k) → Bool → ℕ) (hzero : ∀ h, size none h = 0) :
    digit blue outer b bit v s j (t, fun l => bit (lengths u size l) j) =
      bit ((blue t v).width u outer size s) j := by
  unfold digit Outline.width
  dsimp only
  split_ifs <;> cases hn : (blue t v).name <;> simp [lengths, hzero]

variable [Fintype T] [Fintype X]

open scoped Classical in
/-- Uniform work bound for one metadata bit or width digit. -/
def readCost (T X : Type) [Fintype T] [Fintype X] (k : ℕ) :=
  (3 * Fintype.card X + 2) * Fintype.card T + 1 +
  ((3 * Fintype.card (X ⊕ LengthKey k) + 2) * Fintype.card (T × (LengthKey k → Bool)) + 1)

open scoped Classical in
theorem read_bit (i : ReadOut Y w e b) :
    ∃ g : BitFormula (ReadIn X k b), g.cost ≤ readCost T X k ∧
      ∀ t u (size : Option (B k) → Bool → ℕ), (∀ h, size none h = 0) →
        g.eval (readIn emb b bit t u size) = readOut blue info outer b bit t u size i := by
  rcases i with i|⟨v, s, j⟩
  · obtain ⟨g, hg, hc⟩ := finite_formula emb (fun t => info t i)
    refine ⟨g.rename Sum.inl, ?_, ?_⟩
    · rw [BitFormula.cost_rename]
      exact hc.trans (Nat.le_add_right _ _)
    · intro t u size _
      rw [BitFormula.eval_rename]
      exact hg t
  · obtain ⟨g, hg, hc⟩ := finite_formula (sliceCode emb) (digit blue outer b bit v s j)
    let f : X ⊕ LengthKey k → ReadIn X k b := Sum.map id (fun l => (l, j))
    refine ⟨g.rename f, ?_, ?_⟩
    · rw [BitFormula.cost_rename]
      exact hc.trans (Nat.le_add_left _ _)
    · intro t u size hz
      have hf : readIn emb b bit t u size ∘ f =
          sliceCode emb (t, fun l => bit (lengths u size l) j) := by
        funext x
        cases x <;> rfl
      rw [BitFormula.eval_rename, hf, hg]
      exact digit_eq blue outer b bit v s j t u size hz

open scoped Classical in
/-- The same family of formulas works for all tags and all length words. -/
theorem read_net [Fintype Y] :
    ∃ g : ReadOut Y w e b → BitFormula (ReadIn X k b),
      (∀ t u size, (∀ h, size none h = 0) → ∀ i,
        (g i).eval (readIn emb b bit t u size) = readOut blue info outer b bit t u size i) ∧
      (∀ i, (g i).cost ≤ readCost T X k) ∧
      (∑ i, (g i).cost) ≤ readCost T X k * (Fintype.card Y + 2 ^ w * 2 ^ e) * (b + 1) := by
  choose g hg he using read_bit emb blue info outer b bit
  refine ⟨g, fun t u size h i => he i t u size h, hg, ?_⟩
  calc
    _ ≤ ∑ _ : ReadOut Y w e b, readCost T X k := Finset.sum_le_sum fun i _ => hg i
    _ = readCost T X k * (Fintype.card Y + 2 ^ w * 2 ^ e * b) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, ReadOut,
        Fintype.card_sum, Fintype.card_prod, B, Fintype.card_fin]
      ring
    _ ≤ _ := by
      rw [mul_assoc (readCost T X k)]
      gcongr
      rw [add_mul]
      exact add_le_add (Nat.le_mul_of_pos_right _ (by omega)) (Nat.mul_le_mul_left _ (by omega))

open scoped Classical in
/-- One-hot peer indices and holder locations accompany the role and direction bits. -/
abbrev Flags (w d e k : ℕ) :=
  B w ⊕ (B w × Option (B k)) ⊕ (B w × B e) ⊕
    (B w × B e × Option (B d × B 0 × B e)) ⊕ (B k × B w)

open scoped Classical in
/-- In the case `.inl i`, this construction gives `(a i).live`. -/
def flags (a : Blueprint w d e k) : Flags w d e k → Bool
  | .inl i => (a i).live
  | .inr (.inl (i, h)) => decide ((a i).name = h)
  | .inr (.inr (.inl (i, j))) => (a i).direction j
  | .inr (.inr (.inr (.inl (i, j, h)))) => decide ((a i).peer j = h)
  | .inr (.inr (.inr (.inr (h, i)))) => decide (a.find h = i)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Geometry.Blueprint
end

/-
# Concentration for every accepted geometric proposal

The bounds apply even if a proposal fails the coefficient check.
Only the short quotas and the unchanged exterior wires enter.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Rounds
variable {F K : Type} [Field F] [Finite K] {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g σ ν : ℕ} {x y : Wire} {W : ℝ} {P : Input F x y S.h D T R g W}
  (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  {old : P.V ↪ B S.m} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {nav : B S.m → B d → B S.m} (A : Children.Shows P.adj old (nav, status))
  (hdata : ∀ i, (data i).1 = nav i) (hg : g ≤ D ^ k) (c : U.selectors.obj)
  {x₀ : S.format.obj} (p : S.Presentation x₀ P.diagram) (hd : p.Directed)
  {loc : P.Occupied ↪ B S.m × B S.h} {part : Fin ν → P.Occupied → P.Occupied}
  {E H : P.Occupied → ℕ} (a : P.Occupied → U.Tag S g σ ν)

local notation "Y" => U.advance data status c
local notation "C" => Input.terminalExponent g σ
local notation "plan" => U.complete S loc (fun i => Prod.fst (a i))
local notation "net" => U.graph A hdata hg c

open scoped Classical in
private def coverage {I V : Type} [Fintype V]
    (rows : U.template.format.obj) (G : U.Graph S rows V)
    (b : U.Matrix S) (hv : U.Valid S x₀ rows b) (loc : I ↪ B S.m × B S.h)
    (hc : ∀ v : U.Actors S, (U.localAt S b v).live = true → ((U.split v.1).1,
      v.2.1) ∈ Set.range loc)
    (hf : ∀ v, U.template.frozen rows v = U.fixedChild (U.split v).2) :
    Geometry.Support I (fun i => b (loc i).1 (loc i).2) (fun _ => U.fixedChild)
      (U.admitted S x₀ rows b hv G p hd).term := by
  have eq : U.board S x₀ rows b hv G (U.materialize S x₀ rows b hv p hd) (fun _ => Iff.rfl) =
      U.admitted S x₀ rows b hv G p hd := rfl
  let sup := U.boardSupport S x₀ rows b hv G (U.materialize S x₀ rows b hv p hd) (fun _ => Iff.rfl)
    loc hc U.fixedChild (fun v _ => hf v.1)
  exact Eq.mp (congrArg (fun E : Geometry.Board (U.revised S) (U.overlay S x₀ rows b) x y u =>
    Geometry.Support I (fun i => b (loc i).1 (loc i).2) (fun _ => U.fixedChild) E.term) eq) sup

open scoped Classical in
private theorem admitted_concentrated {V : Type} [Fintype V]
    (rows : U.template.format.obj) (G : U.Graph S rows V)
    (pass : U.passes S loc part E H (T / u) x₀ rows a)
    (fixed : ∀ v, U.template.frozen rows v = U.fixedChild (U.split v).2)
    (cells : Fintype.card V ≤ D ^ C * Fintype.card P.V)
    (full : ∀ v, (G.adj v).card ≤ D ^ C)
    (core : ∀ v, ((G.adj v).filter (fun w => ¬G.frozen v ∧ ¬G.frozen w)).card ≤ 3)
    (he : (∑ v, (E v : ℝ)) * T ≤ 2 * SphereScale.budget g * ((ν : ℝ) + 1) * W)
    (hh : (∑ v, (H v : ℝ)) * D * T ≤ 3 * (D : ℝ) ^ 5 * W) :
    Concentrated P (U.admitted S x₀ rows plan pass.1 G p hd).term (Geometry.overhead g C) n σ := by
  have support := coverage U p hd rows G plan pass.1 loc (U.complete_support S loc _) fixed
  rw [funext (U.complete_here S loc (fun i => (a i).1))] at support
  have hD : 0 < D := lt_of_lt_of_le (by decide) U.large
  have hv : (Fintype.card P.Occupied : ℝ) * D * T ≤ W := by
    simpa only [Input.Occupied, Fintype.card_coe] using P.occupied
  have totals := Geometry.totals (fun v => (a v).1) (fun _
    => U.fixedChild) hD hv he hh pass.2.1 pass.2.2
  exact support.concentrated (P := P) («C» := Input.terminalExponent g σ) (U.admitted_fibers S x₀
    rows plan pass.1 G p hd) hD cells core full totals pass.2.2

open scoped Classical in
theorem approved_term (ok : U.passes S loc part E H (T / u) x₀ (U.advance data status c) a)
    (hk : k = Layout.Sharing.allocation g σ)
    (he : (∑ v, (E v : ℝ)) * T ≤ 2 * SphereScale.budget g * ((ν : ℝ) + 1) * W)
    (hh : (∑ v, (H v : ℝ)) * D * T ≤ 3 * (D : ℝ) ^ 5 * W) :
    Concentrated P (U.admitted S x₀ Y plan ok.1 net p hd).term (Geometry.overhead g C) n σ := by
  exact admitted_concentrated U p hd a Y net ok (fun _ => rfl)
    (U.graph_cells A hg hk) (U.graph_fullDegree A hdata hg c hk) (U.graph_coreDegree A hdata hg c)
      he hh

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
end
