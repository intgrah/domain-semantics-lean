/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Action
public import DomainSemantics.Presheaf.Approximation

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Opposite Presheaf MonoidalCategory

noncomputable abbrev RawAction.arguments := Tm.presheaf ⊗ (ΩLower.presheaf pointedOrder ⋙ forget Preord)

@[implicit_reducible] def RawAction.monotone :
    Subfunctor (arguments.functorHom (ΩLower.presheaf pointedOrder ⋙ forget Preord)) where
  obj _ := {F | ∀ X σ label, Monotone (β := RawValue X.unop) (fun I : RawValue X.unop => F.app X σ (label, I))}
  map f _ h X σ := h X (f ≫ σ)

abbrev RawAction (Γ : Ctx) := RawAction.monotone.toFunctor.obj (op Γ)

noncomputable def RawAction.app {Γ : Ctx} (F : RawAction Γ) (X : Ctxᵒᵖ)
    (p : (op Γ ⟶ X) × Tm.presheaf.obj X) : Preord.of (RawValue X.unop) ⟶ Preord.of (RawValue X.unop) :=
  Preord.ofHom ⟨fun I => F.val.app X p.1 (p.2, I), F.property X p.1 p.2⟩

@[ext] theorem RawAction.ext {Γ : Ctx} {F G : RawAction Γ}
    (h : ∀ X p I, F.app X p I = G.app X p I) : F = G :=
  Subtype.ext (Functor.HomObj.ext_app fun X σ (label, I) => h X (σ, label) I)

noncomputable instance : PartialOrder (RawAction Γ) :=
  PartialOrder.lift (fun F : RawAction Γ => fun X p I => F.app X p I)
    (fun _ _ h => RawAction.ext fun X p I => congr($h X p I))

noncomputable abbrev RawAction.presheaf : Ctxᵒᵖ ⥤ Preord where
  __ := monotone.toFunctor.toPreord (order := fun X => inferInstanceAs (Preorder (RawAction X.unop)))
    (by intro X Y f F G h Z p I; exact h Z (f ≫ p.1, p.2) I)
  obj X := Preord.of (RawAction X.unop)

noncomputable instance : OrderBot (RawAction Γ) where
  bot := {
    val.app X _ := ↾fun _ => (⊥ : RawValue X.unop)
    val.naturality f _ := ConcreteCategory.hom_ext _ _ fun _ => (ΩLower.presheaf_map_bot f.unop).symm
    property _ _ _ _ _ _ := by rfl }
  bot_le F := fun X p I => @bot_le (RawValue X.unop) _ _ (F.app X p I)

@[simp] theorem RawAction.app_map {X Y Z : Ctxᵒᵖ} (f : X ⟶ Y) (F : RawAction X.unop)
    (p : (Y ⟶ Z) × Tm.presheaf.obj Z) :
    (presheaf.map f F).app Z p = F.app Z (f ≫ p.1, p.2) := rfl

noncomputable def RawAction.pullback {Γ Γ₁ : Ctx} (F : RawAction Γ) (σ : Γ₁ ⟶ Γ) : RawAction Γ₁ :=
  RawAction.presheaf.map σ.op F

namespace RawAction

@[simp] theorem app_pullback {Γ₁ Γ₂ Γ₃ : Ctx} (F : RawAction Γ₁)
    (σ₁ : op Γ₁ ⟶ op Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (label : Σ A : Ty Γ₂, Tm Γ₂ A) (I : RawValue Γ₂) :
    F.app _ (σ₁ ≫ σ₂.op, Tm.presheaf.map σ₂.op label) (I.pullback σ₂) = ((F.app _ (σ₁, label) I).pullback σ₂) :=
  congrArg (fun k : arguments.obj (op Γ₂) ⟶ (ΩLower.presheaf pointedOrder ⋙ forget Preord).obj (op Γ₃) =>
    k (label, I)) (F.val.naturality σ₂.op σ₁)

variable {Γ Γ₁ Γ₂ : Ctx}
variable {G : RawAction Γ}

def IsFinitary (F : RawAction Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A),
    ΩLower.IsFinitary (F.app _ (σ.op, label))

theorem IsFinitary.eventually {F : RawAction Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : RawValue Γ₁)
    {y : CoherentShape Γ₁} (hy : (F.app _ (σ.op, label) I).mem (𝟙 Γ₁) y) :
    ∀ᶠ J in I.approximations, (F.app _ (σ.op, label) J).mem (𝟙 Γ₁) y :=
  (hF σ label).eventually (F.app _ (σ.op, label)).hom.monotone ΩLower.eventually_mem hy

def IsIdealValued (F : RawAction Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁), (F.app _ (σ.op, label) I.val).IsDirected

theorem IsFinitary.exists_principal {F : RawAction Γ} (hF : F.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : Domain Γ₁)
    {y : CoherentShape Γ₁} (hy : (F.app _ (σ.op, label) I.val).mem (𝟙 Γ₁) y) :
    ∃ x, I.mem (𝟙 Γ₁) x ∧
      (F.app _ (σ.op, label) (ΩLower.principal pointedOrder x)).mem (𝟙 Γ₁) y :=
  (hF σ label).exists_principal (F.app _ (σ.op, label)).hom.monotone I.property hy

theorem IsFinitary.pullback {F : RawAction Γ} (hF : F.IsFinitary) (σ : Γ₁ ⟶ Γ) :
    IsFinitary (presheaf.map σ.op F) :=
  fun σ₁ => hF (σ₁ ≫ σ)

theorem IsIdealValued.pullback {F : RawAction Γ} (hF : F.IsIdealValued) (σ : Γ₁ ⟶ Γ) :
    IsIdealValued (presheaf.map σ.op F) :=
  fun σ₁ => hF (σ₁ ≫ σ)

noncomputable def onBasis (F : RawAction Γ) : BasisAction Γ where
  app X p := (ΩLower.principalNatTrans pointedOrder).app X ≫ F.app X p
  naturality g p := Preord.ext fun x => by
    change F.app _ (p.1 ≫ g, Tm.presheaf.map g p.2) (ΩLower.principal pointedOrder (reindex g.unop x)) =
      (F.app _ p (ΩLower.principal pointedOrder x)).pullback g.unop
    simpa using F.app_pullback p.1 g.unop p.2 (ΩLower.principal pointedOrder x)

abbrev GraphValid (F : RawAction Γ) (σ : Γ₁ ⟶ Γ) (f : CoherentGraph Γ₁) : Prop :=
  F.onBasis.GraphValid σ f

theorem GraphValid.mono {F : RawAction Γ} (hFG : F ≤ G) {σ : Γ₁ ⟶ Γ}
    {f : CoherentGraph Γ₁} (hf : GraphValid F σ f) : GraphValid G σ f :=
  BasisAction.GraphValid.mono (fun Γ₂ p x => hFG Γ₂ p (ΩLower.principal pointedOrder x)) hf

noncomputable abbrev abstraction (F : RawAction Γ) : RawValue Γ := F.onBasis.abstraction

@[simp]
theorem abstraction_mem {F : RawAction Γ} {σ : Γ₁ ⟶ Γ} {q : CoherentShape Γ₁} :
    F.abstraction.mem σ q ↔ ∃ f : CoherentGraph Γ₁, GraphValid F σ f ∧ q ≤ f.lamGenerator :=
  BasisAction.mem_abstraction F.onBasis σ q

@[simp]
theorem pullback_abstraction (F : RawAction Γ) (σ : Γ₁ ⟶ Γ) :
    F.abstraction.pullback σ = abstraction (presheaf.map σ.op F) :=
  BasisAction.pullback_abstraction F.onBasis σ

theorem abstraction_mono {F : RawAction Γ} (h : F ≤ G) : F.abstraction ≤ G.abstraction :=
  BasisAction.abstraction_mono (fun Γ₁ p x => h Γ₁ p (ΩLower.principal pointedOrder x))

noncomputable def abstractionHom : presheaf ⟶ ΩLower.presheaf pointedOrder where
  app _ := Preord.ofHom { toFun := abstraction, monotone' := fun _ _ => abstraction_mono }
  naturality _ _ σ := Preord.ext fun F => (pullback_abstraction F σ.unop).symm

theorem onBasis_eq_of_eq_on_ideals {F : RawAction Γ}
    (h : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁),
    F.app _ (σ.op, label) I.val = G.app _ (σ.op, label) I.val) : F.onBasis = G.onBasis := by
  ext _ ⟨⟨σ⟩, label⟩ x
  exact h σ label (principalIdeal x)

theorem abstraction_eq_of_eq_on_ideals {F : RawAction Γ}
    (h : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁),
    F.app _ (σ.op, label) I.val = G.app _ (σ.op, label) I.val) : F.abstraction = G.abstraction :=
  congrArg BasisAction.abstraction (onBasis_eq_of_eq_on_ideals h)

theorem abstraction_eq_of_ideal_values (F : RawAction Γ) (K : IdealAction Γ)
    (h : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X : Domain Γ₂),
      F.app _ (σ₁.op, name) X.val = (K.val.app _ (σ₁.op, name) X).val) :
    F.abstraction = (IdealAction.abstraction K).val :=
  congrArg BasisAction.abstraction
    (by ext _ ⟨⟨σ⟩, label⟩ x; exact h σ label (principalIdeal x))

noncomputable def toIdealAction (F : RawAction Γ) (hF : F.IsFinitary) (hD : F.IsIdealValued) :
    IdealAction Γ where
  val.app _ := fun (σ₁, label) => Preord.ofHom {
    toFun I := (F.app _ (σ₁, label) I.val).toIdeal (hD σ₁.unop label I)
    monotone' _ _ h := (F.app _ (σ₁, label)).hom.monotone h }
  val.naturality σ₂ := fun ⟨σ₁, label⟩ => Preord.ext fun I => by
    apply Subtype.val_injective
    change F.app _ (σ₁ ≫ σ₂, Tm.presheaf.map σ₂ label) (I.val.pullback σ₂.unop) =
      (F.app _ (σ₁, label) I.val).pullback σ₂.unop
    exact F.app_pullback σ₁ σ₂.unop label I.val
  property _ a := hF.exists_principal a.1.unop a.2

@[simp]
theorem toIdealAction_value_toLower (F : RawAction Γ) (hF : F.IsFinitary)
    (hD : F.IsIdealValued) (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁) :
    ((F.toIdealAction hF hD).val.app _ (σ.op, label) I).val = F.app _ (σ.op, label) I.val := rfl

theorem abstraction_isDirected (F : RawAction Γ) (hD : F.IsIdealValued) :
    F.abstraction.IsDirected :=
  BasisAction.abstraction_isDirected (fun σ label x => hD σ label (principalIdeal x))

end RawAction

end DomainSemantics.CoherentShape
