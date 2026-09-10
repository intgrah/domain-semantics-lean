/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Action.Basic

@[expose] public section

namespace DomainSemantics

open CategoryTheory Opposite Presheaf

namespace CoherentShape

noncomputable abbrev IdealAction.operations := Functor.parameterizedHom
  (ΩIdeal.presheaf pointedOrder) (ΩIdeal.presheaf pointedOrder)
  Tm.presheaf

@[implicit_reducible] def IdealAction.finitary : Subfunctor (operations ⋙ forget Preord) where
  obj _ := {F | ΩIdeal.Finitary F}
  map _ _ h := h.map _

noncomputable abbrev IdealAction.presheaf := finitary.toPreord

abbrev IdealAction (Γ₁ : Ctx) : Type := IdealAction.presheaf.obj (op Γ₁)

noncomputable def IdealAction.pullback {Γ Γ₁ : Ctx} (F : IdealAction Γ) (σ : Γ₁ ⟶ Γ) : IdealAction Γ₁ :=
  IdealAction.presheaf.map σ.op F

namespace IdealAction

@[simp] theorem app_pullback {Γ₁ Γ₂ Γ₃ : Ctx} (F : IdealAction Γ₁)
    (σ₁ : op Γ₁ ⟶ op Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (label : Σ A : Ty Γ₂, Tm Γ₂ A) (I : Domain Γ₂) :
    F.val.app _ (σ₁ ≫ σ₂.op, Tm.presheaf.map σ₂.op label) (I.pullback σ₂) = ((F.val.app _ (σ₁, label) I).pullback σ₂) :=
  F.val.naturality_apply σ₂.op (σ₁, label) I

noncomputable abbrev onBasis (F : IdealAction Γ) : BasisAction Γ :=
  (Functor.HomObj.ofNatTrans (ΩIdeal.principalNatTrans pointedOrder)).comp F.val |>.comp
    (Functor.HomObj.ofNatTrans (ΩIdeal.toLowerNatTrans pointedOrder))

theorem onBasis_isIdealValued (F : IdealAction Γ) : F.onBasis.IsIdealValued :=
  fun σ label x => (F.val.app _ (σ.op, label) (principalIdeal x)).property

abbrev GraphValid (F : IdealAction Γ) {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (f : CoherentGraph Γ₁) : Prop :=
  F.onBasis.GraphValid σ f

noncomputable def abstraction (F : IdealAction Γ) : Domain Γ :=
  F.onBasis.abstraction.toIdeal (BasisAction.abstraction_isDirected F.onBasis_isIdealValued)

@[simp] theorem mem_abstraction {Γ₁ Γ₂ : Ctx} (F : IdealAction Γ₂)
    (σ₁ : Γ₁ ⟶ Γ₂) (q : CoherentShape Γ₁) :
    (abstraction F).mem σ₁ q ↔ ∃ f : CoherentGraph Γ₁, F.onBasis.GraphValid σ₁ f ∧ q ≤ f.lamGenerator :=
  BasisAction.mem_abstraction F.onBasis σ₁ q

theorem abstraction_mono {F G : IdealAction Γ}
    (h : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
      (I : Domain Γ₁), F.val.app _ (σ.op, label) I ≤ G.val.app _ (σ.op, label) I) :
    abstraction F ≤ abstraction G :=
  BasisAction.abstraction_mono (fun _ ⟨⟨σ⟩, label⟩ x => h σ label (principalIdeal x))

theorem mem_value_of_evaluates {F : IdealAction Γ} {Γ₁ : Ctx}
    {σ : Γ₁ ⟶ Γ} {label : Σ A : Ty Γ₁, Tm Γ₁ A}
    {x y : CoherentShape Γ₁}
    (h : Evaluates ((abstraction F).pullback σ) label x y) :
    (F.val.app _ (σ.op, label) (principalIdeal x)).mem (𝟙 Γ₁) y :=
  h.mem_of_outputAtom (F.val.app _ (σ.op, label) (principalIdeal x)).property
    BasisAction.mem_value_of_outputAtom

theorem evaluates_abstraction_of_mem_value {F : IdealAction Γ}
    {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {label : Σ A : Ty Γ₁, Tm Γ₁ A}
    {x y : CoherentShape Γ₁}
    (h : (F.val.app _ (σ.op, label) (principalIdeal x)).mem (𝟙 Γ₁) y) :
    Evaluates ((abstraction F).pullback σ) label x y :=
  .entry (BasisAction.outputAtom_of_mem_value (F := F.onBasis) h)

@[simp]
theorem application_abstraction (F : IdealAction Γ)
    (label : Σ A : Ty Γ, Tm Γ A)
    (X : Domain Γ) :
    application (abstraction F) label X =
      F.val.app _ ((𝟙 Γ).op, label) X := by
  ext Γ₁ σ y
  let label' := Tm.presheaf.map σ.op label
  have hnatural : (F.val.app _ ((𝟙 Γ).op, label) X).pullback σ =
      F.val.app _ (σ.op, label') (X.pullback σ) := by
    have h := (F.val.naturality_apply σ.op ((𝟙 Γ).op, label) X).symm
    change (F.val.app _ ((𝟙 Γ).op, label) X).pullback σ =
      F.val.app _ ((𝟙 Γ).op ≫ σ.op, label') (X.pullback σ) at h
    simpa using h
  rw [CoherentShape.mem_application]
  constructor
  · intro ⟨x, hx, hxy⟩
    have hx' : (X.pullback σ).mem (𝟙 Γ₁) x :=
      (ΩIdeal.presheaf_map_mem_id X σ x).mpr hx
    have hprincipal : principalIdeal x ≤ (X.pullback σ) :=
      ΩLower.principal_le_iff.mpr hx'
    have hy := (F.val.app _ (σ.op, label')).hom.monotone hprincipal (𝟙 Γ₁) _
      (mem_value_of_evaluates hxy)
    have hy' : ((F.val.app _ ((𝟙 Γ).op, label) X).pullback σ).mem
        (𝟙 Γ₁) y := by
      rw [hnatural]
      exact hy
    exact (ΩIdeal.presheaf_map_mem_id
      (F.val.app _ ((𝟙 Γ).op, label) X) σ y).mp hy'
  · intro hy
    have hy' : (F.val.app _ (σ.op, label') (X.pullback σ)).mem
        (𝟙 Γ₁) y := by
      rw [← hnatural]
      exact (ΩIdeal.presheaf_map_mem_id
        (F.val.app _ ((𝟙 Γ).op, label) X) σ y).mpr hy
    have ⟨x, hx, hxy⟩ := F.property _ (σ.op, label') (X.pullback σ) hy'
    exact ⟨x, (ΩIdeal.presheaf_map_mem_id X σ x).mp hx,
      evaluates_abstraction_of_mem_value hxy⟩

end IdealAction

theorem pullback_abstraction {Γ₁ Γ : Ctx} (F : IdealAction Γ)
    (σ : Γ₁ ⟶ Γ) :
    (IdealAction.abstraction F).pullback σ =
      IdealAction.abstraction (F.pullback σ) :=
  Subtype.val_injective (BasisAction.pullback_abstraction F.onBasis σ)

theorem pullback_application {Γ₁ Γ : Ctx}
    (I X : Domain Γ)
    (label : Σ A : Ty Γ, Tm Γ A) (σ : Γ₁ ⟶ Γ) :
    (application I label X).pullback σ =
      application (I.pullback σ)
        (Tm.presheaf.map σ.op label) (X.pullback σ) := by
  change (_ : Domain Γ₁) = _
  ext Γ₂ σ₁ y
  rw [ΩIdeal.presheaf_map_mem, mem_application, mem_application]
  rw [← ΩIdeal.pullback_pullback, op_comp, Functor.map_comp_apply]
  rfl

end CoherentShape

end DomainSemantics
