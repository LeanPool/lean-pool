/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Tarski.Elementary
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Tarski.AesopInit
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Finset.Card
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Graph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Relations and functions defined by a first-order formula (with parameter)
-/

namespace FFL
namespace FirstOrder

variable {L : Language} {M : Type*} [Tarski.Structure L M]

/-- The Is Defined By construction in `FFL.FirstOrder`. -/
abbrev IsDefinedBy (R : (Fin k → M) → Prop) (φ : Semisentence L k) : Prop :=
  ∀ v, φ.Evalb v ↔ R v

/-- Data and laws for Defined in `FFL.FirstOrder`. -/
class Defined (R : outParam ((Fin k → M) → Prop)) (φ : Semisentence L k) : Prop where
  iff : IsDefinedBy R φ

/-- The relation `R` is definable by a formula `φ` with parameters over the domain `M`.
Here, the free variables of `φ` are indexed by the type `M`, so that `φ` may contain finitely
many parameters, which are interpreted by using `id : M → M` for the valuation of free
variables.
-/
abbrev IsDefinedByWithParam (R : (Fin k → M) → Prop) (φ : Semiformula L M k) : Prop :=
  ∀ v, φ.Eval v id ↔ R v

@[simp]
lemma Defined.eval_iff {R : (Fin k → M) → Prop} {φ : Semisentence L k} [h : Defined R φ] (v) :
    φ.Evalb v ↔ R v :=
  h.iff v

lemma IsDefinedByWithParam.iff {R : (Fin k → M) → Prop} {φ : Semiformula L M k}
    (h : IsDefinedByWithParam R φ) (v) : φ.Eval v id ↔ R v :=
  h v

/-- The Defined Function construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction (f : (Fin k → M) → M) (φ : Semisentence L (k + 1)) : Prop :=
  Defined (fun v ↦ v 0 = f (v ·.succ)) φ

/-- The Defined Pred construction in `FFL.FirstOrder`. -/
abbrev DefinedPred (P : M → Prop) (φ : Semisentence L 1) : Prop :=
  Defined (fun v ↦ P (v 0)) φ

/-- The Defined Rel construction in `FFL.FirstOrder`. -/
abbrev DefinedRel (R : M → M → Prop) (φ : Semisentence L 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ

/-- The Defined Rel₃ construction in `FFL.FirstOrder`. -/
abbrev DefinedRel₃ (R : M → M → M → Prop) (φ : Semisentence L 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ

/-- The Defined Rel₄ construction in `FFL.FirstOrder`. -/
abbrev DefinedRel₄ (R : M → M → M → M → Prop) (φ : Semisentence L 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ

/-- The Defined Function₀ construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction₀ (c : M) (φ : Semisentence L 1) : Prop :=
  DefinedFunction (fun _ => c) φ

/-- The Defined Function₁ construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction₁ (f : M → M) (φ : Semisentence L 2) : Prop :=
  DefinedFunction (fun v ↦ f (v 0)) φ

/-- The Defined Function₂ construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction₂ (f : M → M → M) (φ : Semisentence L 3) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1)) φ

/-- The Defined Function₃ construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction₃ (f : M → M → M → M) (φ : Semisentence L 4) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2)) φ

/-- The Defined Function₄ construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction₄ (f : M → M → M → M → M) (φ : Semisentence L 5) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3)) φ

/-- The Defined Function₅ construction in `FFL.FirstOrder`. -/
abbrev DefinedFunction₅ (f : M → M → M → M → M → M) (φ : Semisentence L 6) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4)) φ

/-- The «term -relation Via » construction in `FFL.FirstOrder`. -/
notation K "-relation " P " via " φ => DefinedRel (L := K) P φ

/-- The «term -relation₃ Via » construction in `FFL.FirstOrder`. -/
notation K "-relation₃ " P " via " φ => DefinedRel₃ (L := K) P φ

/-- The «term -relation₄ Via » construction in `FFL.FirstOrder`. -/
notation K "-relation₄ " P " via " φ => DefinedRel₄ (L := K) P φ

/-- The «term -function₀ Via » construction in `FFL.FirstOrder`. -/
notation K "-function₀ " c " via " φ => DefinedFunction₀ (L := K) c φ

/-- The «term -function₁ Via » construction in `FFL.FirstOrder`. -/
notation K "-function₁ " f " via " φ => DefinedFunction₁ (L := K) f φ

/-- The «term -function₂ Via » construction in `FFL.FirstOrder`. -/
notation K "-function₂ " f " via " φ => DefinedFunction₂ (L := K) f φ

/-- The «term -function₃ Via » construction in `FFL.FirstOrder`. -/
notation K "-function₃ " f " via " φ => DefinedFunction₃ (L := K) f φ

/-- The «term -function₄ Via » construction in `FFL.FirstOrder`. -/
notation K "-function₄ " f " via " φ => DefinedFunction₄ (L := K) f φ

/-- The «term -function₅ Via » construction in `FFL.FirstOrder`. -/
notation K "-function₅ " f " via " φ => DefinedFunction₅ (L := K) f φ

/-- The «term -predicate[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-predicate[" N "] " P " via " φ => DefinedPred (L := K) (M := N) P φ

/-- The «term -relation[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-relation[" N "] " P " via " φ => DefinedRel (L := K) (M := N) P φ

/-- The «term -relation₃[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-relation₃[" N "] " P " via " φ => DefinedRel₃ (L := K) (M := N) P φ

/-- The «term -relation₄[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-relation₄[" N "] " P " via " φ => DefinedRel₄ (L := K) (M := N) P φ

/-- The «term -function₀[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-function₀[" N "] " c " via " φ => DefinedFunction₀ (L := K) (M := N) c φ

/-- The «term -function₁[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-function₁[" N "] " f " via " φ => DefinedFunction₁ (L := K) (M := N) f φ

/-- The «term -function₂[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-function₂[" N "] " f " via " φ => DefinedFunction₂ (L := K) (M := N) f φ

/-- The «term -function₃[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-function₃[" N "] " f " via " φ => DefinedFunction₃ (L := K) (M := N) f φ

/-- The «term -function₄[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-function₄[" N "] " f " via " φ => DefinedFunction₄ (L := K) (M := N) f φ

/-- The «term -function₅[ ] Via » construction in `FFL.FirstOrder`. -/
notation K "-function₅[" N "] " f " via " φ => DefinedFunction₅ (L := K) (M := N) f φ

namespace Language

variable (L)

/-- Data and laws for Definable in `FFL.FirstOrder.Language`. -/
class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ φ : Semiformula L M k, IsDefinedByWithParam P φ

/-- The Definable Pred construction in `FFL.FirstOrder.Language`. -/
abbrev DefinablePred (P : M → Prop) : Prop :=
  L.Definable (k := 1) fun v ↦ P (v 0)

/-- The Definable Rel construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableRel (P : M → M → Prop) : Prop :=
  L.Definable (k := 2) (fun v ↦ P (v 0) (v 1))

/-- The Definable Rel₃ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop :=
  L.Definable (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))

/-- The Definable Rel₄ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableRel₄ (P : M → M → M → M → Prop) : Prop :=
  L.Definable (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))

/-- The Definable Rel₅ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableRel₅ (P : M → M → M → M → M → Prop) : Prop :=
  L.Definable (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))

/-- The Definable Rel₆ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableRel₆ (P : M → M → M → M → M → M → Prop) : Prop :=
  L.Definable (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))

/-- The Definable Function construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction (f : (Fin k → M) → M) : Prop :=
  Definable (k := k + 1) L fun v ↦ v 0 = f (v ·.succ)

/-- The Definable Function₀ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction₀ (c : M) : Prop :=
  L.DefinableFunction (k := 0) (fun _ ↦ c)

/-- The Definable Function₁ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction₁ (f : M → M) : Prop :=
  L.DefinableFunction (k := 1) (fun v ↦ f (v 0))

/-- The Definable Function₂ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction₂ (f : M → M → M) : Prop :=
  L.DefinableFunction (k := 2) (fun v ↦ f (v 0) (v 1))

/-- The Definable Function₃ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction₃ (f : M → M → M → M) : Prop :=
  L.DefinableFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

/-- The Definable Function₄ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction₄ (f : M → M → M → M → M) : Prop :=
  L.DefinableFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))

/-- The Definable Function₅ construction in `FFL.FirstOrder.Language`. -/
abbrev DefinableFunction₅ (f : M → M → M → M → M → M) : Prop :=
  L.DefinableFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))

variable {L}

/-- The «term -predicate » construction in `FFL.FirstOrder.Language`. -/
notation L "-predicate " P => DefinablePred L P

/-- The «term -relation » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation " P => DefinableRel L P

/-- The «term -relation₃ » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation₃ " P => DefinableRel₃ L P

/-- The «term -relation₄ » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation₄ " P => DefinableRel₄ L P

/-- The «term -relation₅ » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation₅ " P => DefinableRel₅ L P

/-- The «term -function₁ » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₁ " f => DefinableFunction₁ L f

/-- The «term -function₂ » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₂ " f => DefinableFunction₂ L f

/-- The «term -function₃ » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₃ " f => DefinableFunction₃ L f

/-- The «term -function₄ » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₄ " f => DefinableFunction₄ L f

/-- The «term -predicate[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-predicate[" N "] " P => DefinablePred (M := N) L P

/-- The «term -relation[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation[" N "] " P => DefinableRel (M := N) L P

/-- The «term -relation₃[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation₃[" N "] " P => DefinableRel₃ (M := N) L P

/-- The «term -relation₄[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation₄[" N "] " P => DefinableRel₄ (M := N) L P

/-- The «term -relation₅[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-relation₅[" N "] " P => DefinableRel₅ (M := N) L P

/-- The «term -function₁[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₁[" N "] " f => DefinableFunction₁ (M := N) L f

/-- The «term -function₂[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₂[" N "] " f => DefinableFunction₂ (M := N) L f

/-- The «term -function₃[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₃[" N "] " f => DefinableFunction₃ (M := N) L f

/-- The «term -function₄[ ] » construction in `FFL.FirstOrder.Language`. -/
notation L "-function₄[" N "] " f => DefinableFunction₄ (M := N) L f

end Language

namespace IsDefinedBy

lemma of_vec_one {R : (Fin 1 → M) → Prop} {φ : Semisentence L 1}
    (h : ∀ x, φ.Evalb ![x] ↔ R ![x]) : IsDefinedBy R φ := by
  intro v;
  simpa [← Matrix.fun_eq_vec_one] using h (v 0)

lemma of_vec_two {R : (Fin 2 → M) → Prop} {φ : Semisentence L 2}
    (h : ∀ x y, φ.Evalb ![x, y] ↔ R ![x, y]) : IsDefinedBy R φ := by
  intro v;
  simpa [← Matrix.fun_eq_vec_two] using h (v 0) (v 1)

lemma of_vec_three {R : (Fin 3 → M) → Prop} {φ : Semisentence L 3}
    (h : ∀ x y z, φ.Evalb ![x, y, z] ↔ R ![x, y, z]) : IsDefinedBy R φ := by
  intro v;
  simpa [← Matrix.fun_eq_vec_three] using h (v 0) (v 1) (v 2)

end IsDefinedBy

namespace Defined

lemma to_definable {R : (Fin k → M) → Prop} {φ : Semisentence L k} (hR : Defined R φ) :
    L.Definable R :=
  ⟨Rewriting.emb φ, fun v ↦ by simp [Semiformula.eval_emb]⟩

end Defined

namespace DefinedFunction

lemma to_definable {f : (Fin k → M) → M} {φ : Semisentence L (k + 1)}
    (hf : DefinedFunction f φ) : L.DefinableFunction f :=
  Defined.to_definable hf

end DefinedFunction

namespace Language

namespace Definable

variable {P Q R : (Fin k → M) → Prop}

lemma of_iff {P Q : (Fin k → M) → Prop} (H : L.Definable Q) (h : ∀ x, P x ↔ Q x) :
    L.Definable P := by rwa [show P = Q from by funext v; simp [h]]

@[simp]
lemma const (p : Prop) : L.Definable fun _ : Fin k → M ↦ p :=
  by
  by_cases hp : p
  · exact ⟨⊤, by intro _; simp [hp]⟩
  · exact ⟨⊥, by intro _; simp [hp]⟩

@[grind .]
lemma and {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ∧ S v :=
  by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋏ ψ, by intro _; simp [hR.iff, hS.iff]⟩

@[grind .]
lemma or {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ∨ S v :=
  by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋎ ψ, by intro _; simp [hR.iff, hS.iff]⟩

@[grind .]
lemma imp {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v → S v :=
  by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⇒ₗ ψ, by intro _; simp [hR.iff, hS.iff]⟩

@[grind .]
lemma not {R : (Fin k → M) → Prop} (hR : L.Definable R) :
    L.Definable fun v : Fin k → M ↦ ¬R v :=
  by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∼φ, by intro _; simp [hR.iff]⟩

@[grind .]
lemma biconditional {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ↔ S v :=
  by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⇔ₗ ψ, by intro _; simp [hR.iff, hS.iff]⟩

lemma all {R : (Fin k → M) → M → Prop} (hR : L.Definable fun w ↦ R (w ·.succ) (w 0)) :
    L.Definable fun v : Fin k → M ↦ ∀ x, R v x :=
  by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∀¹ φ, fun v ↦ by simp [hR.iff]⟩

lemma exs {R : (Fin k → M) → M → Prop} (hR : L.Definable fun w ↦ R (w ·.succ) (w 0)) :
    L.Definable fun v : Fin k → M ↦ ∃ x, R v x :=
  by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∃¹ φ, fun v ↦ by simp [hR.iff]⟩

instance eq [L.Eq] [Tarski.Structure.Eq L M] : L-relation[M] Eq :=
  ⟨“x y. x = y”, fun _ ↦ by simp⟩

instance lt [L.LT] [LT M] [Tarski.Structure.LT L M] : L-relation[M] _root_.LT.lt :=
  ⟨“x y. x < y”, fun _ ↦ by simp⟩

instance mem [L.Mem] [Membership M M] [Tarski.Structure.Mem L M] :
    L-relation[M] Membership.mem :=
  ⟨“x y. y ∈ x”, fun _ ↦ by simp⟩

lemma fconj {P : ι → (Fin k → M) → Prop} (s : Finset ι)
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) :
    L.Definable fun v : Fin k → M ↦ ∀ i ∈ s, P i v :=
  by
  have : ∀ i, ∃ φ, IsDefinedByWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⋀ i ∈ s, φ i, fun v ↦ by simp [fun i ↦ (H i).iff]⟩

lemma fdisj {P : ι → (Fin k → M) → Prop} (s : Finset ι)
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) :
    L.Definable fun v : Fin k → M ↦ ∃ i ∈ s, P i v :=
  by
  have : ∀ i, ∃ φ, IsDefinedByWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⋁ i ∈ s, φ i, fun v ↦ by simp [fun i ↦ (H i).iff]⟩

lemma fintype_all {ι : Type*} [_root_.Finite ι] {P : ι → (Fin k → M) → Prop}
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) :
    L.Definable fun v : Fin k → M ↦ ∀ i, P i v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  simpa using fconj Finset.univ h

lemma fintype_exs {ι : Type*} [_root_.Finite ι] {P : ι → (Fin k → M) → Prop}
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) :
    L.Definable fun v : Fin k → M ↦ ∃ i, P i v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  simpa using fdisj Finset.univ h

lemma retraction (h : L.Definable P) {n} (f : Fin k → Fin n) :
    L.Definable fun v ↦ P (fun i ↦ v (f i)) :=
  by
  rcases h with ⟨φ, hφ⟩
  exact ⟨(Rew.subst fun i ↦ #(f i)) ▹ φ, fun v ↦ by simp [← hφ.iff, Function.comp_def]⟩

lemma exsVec {k l} {P : (Fin k → M) → (Fin l → M) → Prop}
    (h :
      L.Definable fun w : Fin (k + l) → M ↦
        P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    L.Definable fun v : Fin k → M ↦ ∃ ys : Fin l → M, P v ys :=
  by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l
    ih =>
    suffices L.Definable fun v : Fin k → M ↦ ∃ y, ∃ ys : Fin l → M, P v (y :> ys)
      by
      apply of_iff this; intro x
      constructor
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
    apply exs; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l)
        (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact
      of_iff (retraction h g)
        (by
          intro v; simp only [g]
          apply iff_of_eq; congr
          · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · ext i
            refine Fin.cases ?_ (fun i => ?_) i
            · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
            · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → M) → (Fin l → M) → Prop}
    (h :
      L.Definable fun w : Fin (k + l) → M ↦
        P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    L.Definable fun v : Fin k → M ↦ ∀ ys : Fin l → M, P v ys :=
  by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l
    ih =>
    suffices L.Definable fun v : Fin k → M ↦ ∀ y, ∀ ys : Fin l → M, P v (y :> ys)
      by
      apply of_iff this; intro x
      constructor
      · intro h y ys; apply h
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) :=
      Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l)
        (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact
      of_iff (retraction h g)
        (by
          intro v; simp only [g]
          apply iff_of_eq; congr
          · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
          · ext i
            refine Fin.cases ?_ (fun i => ?_) i
            · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
            · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma substitution {P : (Fin k → M) → Prop} {f : Fin k → (Fin l → M) → M} (hP : L.Definable P)
    (hf : ∀ i, L.DefinableFunction (f i)) : L.Definable fun z ↦ P (f · z) :=
  by
  have : L.Definable fun z ↦ ∃ ys : Fin k → M, (∀ i, ys i = f i z) ∧ P ys :=
    by
    apply exsVec; apply and
    · apply fintype_all; intro i
      simpa using retraction (hf i) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact
    of_iff this <| by
      intro v
      constructor
      · intro hP
        exact ⟨(f · v), by simp, hP⟩
      · rintro ⟨ys, hys, hP⟩
        have : ys = fun i ↦ f i v := funext hys
        rcases this; exact hP

end Definable

lemma DefinablePred.comp {P : M → Prop} {k} {f : (Fin k → M) → M} [hP : L.DefinablePred P]
    (hf : L.DefinableFunction f) : L.Definable (fun v ↦ P (f v)) :=
  Definable.substitution (f := ![f]) hP (by simpa using hf)

lemma DefinableRel.comp {P : M → M → Prop} {k} {f g : (Fin k → M) → M} [hP : L.DefinableRel P]
    (hf : L.DefinableFunction f) (hg : L.DefinableFunction g) :
    L.Definable fun v ↦ P (f v) (g v) :=
  Definable.substitution (f := ![f, g]) hP
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf, hg])

lemma DefinableRel₃.comp {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hP : L.DefinableRel₃ P] (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) : L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃]) hP
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma DefinableRel₄.comp {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hP : L.DefinableRel₄ P] (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄]) hP
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma DefinableRel₅.comp {k} {P : M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    [hP : L.DefinableRel₅ P] (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄)
    (hf₅ : L.DefinableFunction f₅) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hP
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])

lemma DefinablePred.of_iff {P Q : M → Prop} (H : L.DefinablePred Q) (h : ∀ x, P x ↔ Q x) :
    L.DefinablePred P := by rwa [show P = Q from by funext v; simp [h]]

instance DefinableFunction₁.graph {f : M → M} [h : L.DefinableFunction₁ f] :
    L.DefinableRel (Function.Graph f) :=
  h

instance DefinableFunction₂.graph {f : M → M → M} [h : L.DefinableFunction₂ f] :
    L.DefinableRel₃ (Function.Graph₂ f) :=
  h

instance DefinableFunction₃.graph {f : M → M → M → M} [h : L.DefinableFunction₃ f] :
    L.DefinableRel₄ (Function.Graph₃ f) :=
  h

/-!
### Definable functions
-/

variable [L.Eq] [Tarski.Structure.Eq L M]

namespace DefinableFunction

instance projection (i : Fin k) : L.DefinableFunction fun w : Fin k → M ↦ w i :=
  ⟨“x. x = #i.succ”, fun _ ↦ by simp⟩

instance const (c : M) : L.DefinableFunction fun _ : Fin k → M ↦ c :=
  ⟨“x. x = &c”, fun _ ↦ by simp⟩

lemma substitution {f : Fin k → (Fin l → M) → M} (hF : L.DefinableFunction F)
    (hf : ∀ i, L.DefinableFunction (f i)) : L.DefinableFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using
    Definable.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <|
      by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using projection _
      · simpa using Definable.retraction (hf i) (0 :> (·.succ.succ))

instance hAdd [L.Add] [Add M] [Tarski.Structure.Add L M] : L-function₂[M] HAdd.hAdd :=
  ⟨“x y z. x = y + z”, fun _ ↦ by simp⟩

instance hMul [L.Mul] [Mul M] [Tarski.Structure.Mul L M] : L-function₂[M] HMul.hMul :=
  ⟨“x y z. x = y * z”, fun _ ↦ by simp⟩

end DefinableFunction

lemma DefinableFunction₁.comp {k} {F : M → M} {f : (Fin k → M) → M}
    [hF : L.DefinableFunction₁ F] (hf : L.DefinableFunction f) :
    L.DefinableFunction (fun v ↦ F (f v)) :=
  DefinableFunction.substitution (f := ![f]) hF (by simp [hf])

lemma DefinableFunction₂.comp {k} {F : M → M → M} {f₁ f₂ : (Fin k → M) → M}
    [hF : L.DefinableFunction₂ F] (hf₁ : L.DefinableFunction f₁)
    (hf₂ : L.DefinableFunction f₂) : L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂]) hF
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₃.comp {k} {F : M → M → M → M} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hF : L.DefinableFunction₃ F] (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) : L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃]) hF
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₄.comp {k} {F : M → M → M → M → M} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hF : L.DefinableFunction₄ F] (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄]) hF
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₅.comp {k} {F : M → M → M → M → M → M} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    [hF : L.DefinableFunction₅ F] (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄)
    (hf₅ : L.DefinableFunction f₅) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hF
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

section aesop

open Lean.Parser.Tactic (config)

attribute [aesop (rule_sets := [Definability]) norm] Function.comp_def

attribute [aesop 4 (rule_sets := [Definability]) safe] DefinableFunction.const
  DefinableFunction.projection Definable.const

attribute [aesop 5 (rule_sets := [Definability]) safe] DefinableFunction₁.comp
  DefinableFunction₂.comp DefinableFunction₃.comp

attribute [aesop 6 (rule_sets := [Definability]) safe] DefinablePred.comp DefinableRel.comp
  DefinableRel₃.comp DefinableRel₄.comp

attribute [aesop 10 (rule_sets := [Definability]) safe] Definable.not Definable.imp
  Definable.biconditional

attribute [aesop 11 (rule_sets := [Definability]) safe] Definable.and Definable.or Definable.all
  Definable.exs

/-- The attr Definability construction in `FFL.FirstOrder.Language`. -/
macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)







/-- The tactic Definability construction in `FFL.FirstOrder.Language`. -/
macro "definability" (config)? : tactic =>
  `(tactic|
    aesop  (config := { terminal := true })
       (rule_sets := [$(Lean.mkIdent `Definability):ident]))

/-- The tactic Definability? construction in `FFL.FirstOrder.Language`. -/
macro "definability?" (config)? : tactic =>
  `(tactic|
    aesop?  (config := { terminal := true })
       (rule_sets := [$(Lean.mkIdent `Definability):ident]))

end aesop

end Language

end FirstOrder
end FFL

end

end PointwiseComposition
