/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Basic
public import LeanPool.PointwiseComposition.Foundation.Meta.ClProver

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Abstract incompleteness theorems and related results
-/

namespace FFL

open FFL.Entailment

namespace FirstOrder

variable {L₀ L : Language}

/-- The Referenceable By construction in `FFL.FirstOrder.Language`. -/
abbrev Language.ReferenceableBy (L L₀ : Language) :=
  Semiterm.Operator.GödelNumber L₀ (Sentence L)

namespace ProvabilityAbstraction

/-- Data and laws for Provability in `FFL.FirstOrder.ProvabilityAbstraction`. -/
structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  /-- The prov construction in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
  prov : Semisentence L₀ 1
  /-- Derivability condition `D1` -/
  bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]

namespace Provability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

/-- The pr construction in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
@[coe]
def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ :=
  𝔅.prov/[⌜σ⌝]

instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) :=
  ⟨pr⟩

/-- The con construction in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
def con (𝔅 : Provability T₀ T) : Sentence L₀ :=
  ∼𝔅 ⊥

/-- The dia construction in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ :=
  ∼𝔅 (∼φ)

end Provability

section

namespace Provability

section

variable {L₀ L : Language} [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

lemma D1 {𝔅 : Provability T₀ T} {σ : Sentence L} : T ⊢ σ → T₀ ⊢ 𝔅 σ := fun h ↦ 𝔅.bew_def h

/-- Data and laws for HBL2 in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ ⇒ₗ τ) ⇒ₗ 𝔅 σ ⇒ₗ 𝔅 τ

export HBL2 (D2)

variable [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

/-- Data and laws for HBL3 in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class HBL3 where
  D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ ⇒ₗ 𝔅 (𝔅 σ)

export HBL3 (D3)

/-- Data and laws for HBL in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class HBL extends 𝔅.HBL2, 𝔅.HBL3

/-- Data and laws for Mono in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class Mono [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  mono {σ τ : Sentence L} : T ⊢ σ ⇒ₗ τ → T₀ ⊢ 𝔅 σ ⇒ₗ 𝔅 τ

export Mono (mono)

/-- Data and laws for Ext in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class Ext [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  ext {σ τ : Sentence L} : T ⊢ σ ⇔ₗ τ → T₀ ⊢ 𝔅 σ ⇔ₗ 𝔅 τ

export Ext (ext)

/-- Data and laws for Rosser in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class Rosser [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ

export Rosser (Ros)

/-- Abstract version of formalized `Γ`-completeness for provability `𝔅`.

  example: `[∀ σ ∈ Σ₁, 𝔅.FormalizedCompleteOn σ]` for formalized `Σ₁`-completeness.
-/
class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where
  formalized_complete_on : T₀ ⊢ σ ⇒ₗ 𝔅 σ

export FormalizedCompleteOn (formalized_complete_on)

attribute [simp, grind .] formalized_complete_on

instance [∀ σ, 𝔅.FormalizedCompleteOn (𝔅 σ)] : 𝔅.HBL3 :=
  ⟨by simp⟩

/-- NOTE: Named after [Vis21].
-/
class Kreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  KR {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ

export Kreisel (KR)

attribute [grind .] KR

/-- Data and laws for Sound On in `FFL.FirstOrder.ProvabilityAbstraction.Provability`. -/
class SoundOn [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T)
    (M : outParam Type*) [Nonempty M] [Tarski.Structure L₀ M] where
  sound_on {σ : Sentence L} : M↓[L₀] ⊧ (𝔅 σ : Sentence L₀) → T ⊢ σ

export SoundOn (sound_on)

attribute [grind .] sound_on

omit [L.ReferenceableBy L₀] in
lemma syntactical_sound {T₀ T : Theory L} {𝔅 : Provability T₀ T} (M : Type*) [Nonempty M]
    [Tarski.Structure L M] [SoundOn 𝔅 M] [M↓[L] ⊧* T₀] : ∀ {σ : Sentence L}, T₀ ⊢ 𝔅 σ → T ⊢ σ :=
  by
  intro σ h; apply 𝔅.sound_on; apply models_of_provable (L := L) (T := T₀); · infer_instance;
  · exact h;

end

section

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma bew_distribute_imply [𝔅.HBL2] (h : T₀ ⊢ 𝔅 (σ ⇒ₗ τ)) : T₀ ⊢ 𝔅 σ ⇒ₗ 𝔅 τ :=
  D2⨀h

instance [𝔅.HBL2] : 𝔅.Mono :=
  ⟨fun h => bew_distribute_imply <| D1 h⟩

instance [𝔅.HBL2] : 𝔅.Ext :=
  ⟨fun h => E_intro (mono (K_left h)) (mono (K_right h))⟩

lemma bew_distribute_and [𝔅.HBL2] : T₀ ⊢ 𝔅 (σ ⋏ τ) ⇒ₗ 𝔅 σ ⋏ 𝔅 τ := by
  have h₁ : T₀ ⊢ 𝔅 (σ ⋏ τ) ⇒ₗ 𝔅 σ := bew_distribute_imply <| D1 and₁;
  have h₂ : T₀ ⊢ 𝔅 (σ ⋏ τ) ⇒ₗ 𝔅 τ := bew_distribute_imply <| D1 and₂; cl_prover[h₁, h₂];

lemma bew_distribute_and' [𝔅.HBL2] : T₀ ⊢ 𝔅 (σ ⋏ τ) → T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ := fun h =>
  bew_distribute_and⨀h

lemma bew_collect_and [𝔅.HBL2] : T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ ⇒ₗ 𝔅 (σ ⋏ τ) :=
  by
  have h₁ : T₀ ⊢ 𝔅 σ ⇒ₗ 𝔅 (τ ⇒ₗ σ ⋏ τ) := 𝔅.mono <| by cl_prover
  have h₂ : T₀ ⊢ 𝔅 (τ ⇒ₗ σ ⋏ τ) ⇒ₗ 𝔅 τ ⇒ₗ 𝔅 (σ ⋏ τ) := D2; cl_prover[h₁, h₂];

lemma dia_mono [𝔅.Mono] (h : T ⊢ σ ⇒ₗ τ) : T₀ ⊢ 𝔅.dia σ ⇒ₗ 𝔅.dia τ :=
  by
  have : T₀ ⊢ 𝔅 (∼τ) ⇒ₗ 𝔅 (∼σ) := 𝔅.mono <| by cl_prover[h];
  cl_prover[this]

end

section

variable [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ≼ T] {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma mono' [𝔅.Mono] (h : T₀ ⊢ σ ⇒ₗ τ) : T₀ ⊢ 𝔅 σ ⇒ₗ 𝔅 τ :=
  𝔅.mono <| WeakerThan.pbl h

lemma ext' [𝔅.Ext] (h : T₀ ⊢ σ ⇔ₗ τ) : T₀ ⊢ 𝔅 σ ⇔ₗ 𝔅 τ :=
  𝔅.ext <| WeakerThan.pbl h

end

end Provability

end

/-- Data and laws for Diagonalization in `FFL.FirstOrder.ProvabilityAbstraction`. -/
class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  /-- The fixedpoint construction in `FFL.FirstOrder.ProvabilityAbstraction.Diagonalization`. -/
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ ⇔ₗ θ/[⌜fixedpoint θ⌝]

open FFL.Entailment Diagonalization Provability

variable [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] {𝔅 : Provability T₀ T}

/-- The gödel construction in `FFL.FirstOrder.ProvabilityAbstraction`. -/
def gödel (𝔅 : Provability T₀ T) : Sentence L :=
  fixedpoint T₀ (“x. ¬!𝔅.prov x”)

lemma gödel_spec : T₀ ⊢ (gödel 𝔅) ⇔ₗ ∼𝔅 (gödel 𝔅) := by
  simpa [gödel, Provability.pr] using diag (“x. ¬!𝔅.prov x”);

section First

variable [L.DecidableEq]

variable [T₀ ≼ T] [Consistent T]

omit [L.DecidableEq] in
theorem unprovable_gödel : T ⊬ (gödel 𝔅) :=
  by
  intro h; have h₁ : T ⊢ 𝔅 (gödel 𝔅) := WeakerThan.pbl <| D1 h;
  have h₂ : T ⊢ (gödel 𝔅) ⇔ₗ ∼𝔅 (gödel 𝔅) := WeakerThan.pbl <| gödel_spec;
  have : T ⊢ ⊥ := by cl_prover[h₁, h₂, h];
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this;
  contradiction

omit [L.DecidableEq] in
theorem unrefutable_gödel [𝔅.Kreisel] : T ⊬ ∼(gödel 𝔅) :=
  by
  intro h₂;
  have h₁ : T ⊢ (gödel 𝔅) := WeakerThan.pbl <| 𝔅.KR <| by cl_prover[gödel_spec (T₀ := T₀), h₂];
  have : T ⊢ ⊥ := (N_iff_CO.mp <| WeakerThan.pbl <| h₂)⨀h₁;
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this
  contradiction;

omit [L.DecidableEq] in
theorem gödel_independent [𝔅.Kreisel] : Independent T (gödel 𝔅) :=
  by
  constructor
  · apply unprovable_gödel
  · apply unrefutable_gödel

omit [L.DecidableEq] in
theorem first_incompleteness [𝔅.Kreisel] : Incomplete T :=
  incomplete_def.mpr ⟨(gödel 𝔅), gödel_independent⟩

end First

section Second

variable [𝔅.HBL]

omit [Diagonalization T₀] in
lemma formalized_consistent_of_existance_unprovable [L.DecidableEq] : T₀ ⊢ ∼𝔅 σ ⇒ₗ 𝔅.con :=
  contra <| mdp D2 <| D1 efq

local notation "𝐆" => gödel 𝔅

variable [L.DecidableEq] [T₀ ≼ T]

omit [L.DecidableEq] in
/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_gödel : T₀ ⊢ 𝔅.con ⇒ₗ ∼𝔅 𝐆 :=
  by
  suffices T₀ ⊢ ∼𝔅 ⊥ ⇒ₗ ∼𝔅 𝐆 from this
  have h₁ : T₀ ⊢ 𝔅 𝐆 ⇒ₗ 𝔅 (𝔅 𝐆) := D3
  have h₂ : T₀ ⊢ 𝔅 𝐆 ⇒ₗ 𝔅 (𝔅 𝐆 ⇒ₗ ⊥) := 𝔅.mono' <| by cl_prover[gödel_spec (T₀ := T₀)]
  have h₃ : T₀ ⊢ 𝔅 (𝔅 𝐆 ⇒ₗ ⊥) ⇒ₗ 𝔅 (𝔅 𝐆) ⇒ₗ 𝔅 ⊥ := D2
  cl_prover[h₁, h₂, h₃]

theorem gödel_iff_con : T₀ ⊢ 𝐆 ⇔ₗ 𝔅.con :=
  by
  have h₁ : T₀ ⊢ ∼𝔅 𝐆 ⇒ₗ 𝔅.con := formalized_consistent_of_existance_unprovable
  have h₂ : T₀ ⊢ 𝔅.con ⇒ₗ ∼𝔅 𝐆 := formalized_unprovable_gödel
  have h₃ : T₀ ⊢ 𝐆 ⇔ₗ ∼𝔅 𝐆 := gödel_spec
  cl_prover[h₁, h₂, h₃];

theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con :=
  by
  intro h
  have : T₀ ⊢ 𝐆 ⇔ₗ 𝔅.con := gödel_iff_con
  have : T ⊢ 𝐆 := by cl_prover[h, this]
  exact unprovable_gödel this

theorem con_unrefutable [Consistent T] [𝔅.Kreisel] : T ⊬ ∼𝔅.con :=
  by
  intro h
  have : T ⊢ 𝐆 ⇔ₗ 𝔅.con := WeakerThan.pbl <| gödel_iff_con;
  have : T ⊢ ∼𝐆 := by cl_prover[h, this]
  exact unrefutable_gödel this

theorem con_independent [Consistent T] [𝔅.Kreisel] : Independent T 𝔅.con :=
  by
  constructor
  · apply con_unprovable
  · apply con_unrefutable

end Second

section Löb

/-- The kreisel construction in `FFL.FirstOrder.ProvabilityAbstraction`. -/
def kreisel (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L :=
  fixedpoint T₀ (“x. !𝔅.prov x → !σ”)

variable {σ : Sentence L}

local notation "𝐊" => kreisel 𝔅

lemma kreisel_spec : T₀ ⊢ (𝐊 σ) ⇔ₗ (𝔅 (𝐊 σ) ⇒ₗ σ) :=
  by
  have := diag (T := T₀) (“x. !𝔅.prov x → !σ”)
  simpa [kreisel, Provability.pr, Rew.subst_comp_subst, ← TransitiveRewriting.comp_app] using
    this;

private lemma kreisel_specAux₂ : T₀ ⊢ (𝔅 (𝐊 σ) ⇒ₗ σ) ⇒ₗ (𝐊 σ) :=
  K_right kreisel_spec

variable [𝔅.HBL]

private lemma kreisel_specAux₁ [T₀ ≼ T] : T₀ ⊢ 𝔅 (𝐊 σ) ⇒ₗ 𝔅 σ :=
  Entailment.mdp₁ (C_trans (mdp D2 (D1 (WeakerThan.pbl <| K_left (kreisel_spec)))) D2) D3

variable [L.DecidableEq] [T₀ ≼ T]

omit [L.DecidableEq] in
theorem löb_theorem (H : T ⊢ 𝔅 σ ⇒ₗ σ) : T ⊢ σ := by
  have d₁ : T ⊢ 𝔅 (𝐊 σ) ⇒ₗ σ := C_trans (WeakerThan.pbl kreisel_specAux₁) H;
  have d₂ : T ⊢ 𝔅 (𝐊 σ) := WeakerThan.pbl <| D1 <| WeakerThan.pbl kreisel_specAux₂⨀d₁;
  exact d₁⨀d₂;

omit [L.DecidableEq] in
theorem formalized_löb_theorem : T₀ ⊢ 𝔅 (𝔅 σ ⇒ₗ σ) ⇒ₗ 𝔅 σ := by
  have h₁ : T₀ ⊢ 𝔅 (𝐊 σ) ⇒ₗ 𝔅 σ := kreisel_specAux₁;
  have h₂ : T₀ ⊢ (𝔅 σ ⇒ₗ σ) ⇒ₗ (𝔅 (𝐊 σ) ⇒ₗ σ) := CCC_of_C_left h₁;
  have h₃ : T ⊢ (𝔅 σ ⇒ₗ σ) ⇒ₗ 𝐊 σ :=
    WeakerThan.pbl <| C_trans (CCC_of_C_left h₁) kreisel_specAux₂;
  exact C_trans (D2⨀(D1 h₃)) h₁;

lemma formalized_unprovable_not_con [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con ⇒ₗ ∼𝔅 (∼𝔅.con) := by
  by_contra hC; have : T ⊢ ∼𝔅.con := löb_theorem <| CN_of_CN_right hC;
  have : T ⊬ ∼𝔅.con := con_unrefutable; contradiction;

lemma formalized_unrefutable_gödel [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con ⇒ₗ ∼𝔅 (∼(gödel 𝔅)) :=
  by
  by_contra hC; have : T ⊬ 𝔅.con ⇒ₗ ∼𝔅 (∼𝔅.con) := formalized_unprovable_not_con;
  have : T ⊢ 𝔅.con ⇒ₗ ∼𝔅 (∼𝔅.con) :=
    C_trans hC <|
      WeakerThan.pbl <| K_left <| ENN_of_E <| 𝔅.ext <| ENN_of_E <| WeakerThan.pbl gödel_iff_con
  contradiction;

end Löb

section Rosser

variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ≼ T] [Consistent T] {𝔅 : Provability T₀ T}

local notation "𝐑" => gödel 𝔅

theorem unrefutable_rosser [𝔅.Rosser] : T ⊬ ∼𝐑 := by
  intro hnρ;
  have hρ : T ⊢ 𝐑 := WeakerThan.pbl <| (K_right gödel_spec)⨀(Ros hnρ);
  have : ¬Consistent T :=
    not_consistent_iff_inconsistent.mpr <|
      inconsistent_iff_provable_bot.mpr <| (N_iff_CO.mp hnρ)⨀hρ;
  contradiction

theorem rosser_independent [𝔅.Rosser] : Independent T 𝐑 :=
  by
  constructor
  · apply unprovable_gödel
  · apply unrefutable_rosser

theorem rosser_first_incompleteness (𝔅 : Provability T₀ T) [𝔅.Rosser] : Incomplete T :=
  incomplete_def.mpr ⟨gödel 𝔅, rosser_independent⟩

omit [Diagonalization T₀] [Consistent T] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable from `T`. -/
theorem kreisel_remark [𝔅.Rosser] : T ⊢ 𝔅.con := by
  have : T₀ ⊢ ∼𝔅 ⊥ := Ros (N_iff_CO.mpr (by simp)); exact WeakerThan.pbl <| this;

end Rosser

end ProvabilityAbstraction

end FirstOrder

end FFL

end

end PointwiseComposition
