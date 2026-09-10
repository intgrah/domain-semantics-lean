/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.Operator

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Opposite Presheaf

namespace IdealOperator

noncomputable def identity : IdealOperator Γ := ⟨Functor.HomObj.id _, ΩIdeal.Finitary.id⟩

def IsIdempotent (P : IdealOperator Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (X : Domain Γ₁),
    P.val.app _ σ.op (P.val.app _ σ.op X) = P.val.app _ σ.op X

theorem IsIdempotent.pullback {P : IdealOperator Γ} (hP : P.IsIdempotent)
    (σ : Γ₁ ⟶ Γ) : IsIdempotent (P.pullback σ) :=
  fun σ₁ ↦ hP (σ₁ ≫ σ)

end IdealOperator

noncomputable abbrev DependentOperator.operations := Functor.parameterizedHom
  (ΩIdeal.presheaf pointedOrder ⊗ ΩIdeal.presheaf pointedOrder)
  (ΩIdeal.presheaf pointedOrder) Tm.presheaf

abbrev DependentOperator.finitary : Subfunctor (operations ⋙ forget Preord) where
  obj Γ₁ := {Q |
    (∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁.unop) (label : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X Y : Domain Γ₂) {z : CoherentShape Γ₂},
      (Q.app _ (σ₁.op, label) (X, Y)).mem (𝟙 Γ₂) z →
        ∃ x, X.mem (𝟙 Γ₂) x ∧ (Q.app _ (σ₁.op, label) (principalIdeal x, Y)).mem (𝟙 Γ₂) z) ∧
    (∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁.unop) (label : Σ A : Ty Γ₂, Tm Γ₂ A)
      (X Y : Domain Γ₂) {z : CoherentShape Γ₂},
      (Q.app _ (σ₁.op, label) (X, Y)).mem (𝟙 Γ₂) z →
        ∃ y, Y.mem (𝟙 Γ₂) y ∧ (Q.app _ (σ₁.op, label) (X, principalIdeal y)).mem (𝟙 Γ₂) z)}
  map σ₁ _ h := ⟨fun σ₂ => h.1 (σ₂ ≫ σ₁.unop), fun σ₂ => h.2 (σ₂ ≫ σ₁.unop)⟩

noncomputable abbrev DependentOperator.presheaf := finitary.toPreord

abbrev DependentOperator (Γ₁ : Ctx) : Type := DependentOperator.presheaf.obj (op Γ₁)

noncomputable def DependentOperator.pullback {Γ Γ₁ : Ctx} (Q : DependentOperator Γ) (σ : Γ₁ ⟶ Γ) :
    DependentOperator Γ₁ := DependentOperator.presheaf.map σ.op Q

theorem DependentOperator.pullback_id {Γ : Ctx} (Q : DependentOperator Γ) : Q.pullback (𝟙 Γ) = Q :=
  DependentOperator.presheaf.map_id_apply (op Γ) Q

theorem DependentOperator.pullback_pullback {Γ Γ₁ Γ₂ : Ctx} (Q : DependentOperator Γ)
    (σ : Γ₁ ⟶ Γ) (σ₁ : Γ₂ ⟶ Γ₁) : (Q.pullback σ).pullback σ₁ = Q.pullback (σ₁ ≫ σ) :=
  (DependentOperator.presheaf.map_comp_apply σ.op σ₁.op Q).symm

namespace DependentOperator

@[simp] theorem app_pullback {Γ₁ Γ₂ Γ₃ : Ctx} (Q : DependentOperator Γ₁)
    (σ₁ : op Γ₁ ⟶ op Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (label : Σ A : Ty Γ₂, Tm Γ₂ A)
    (X Y : Domain Γ₂) :
    Q.val.app _ (σ₁ ≫ σ₂.op, Tm.presheaf.map σ₂.op label)
      ((X.pullback σ₂), (Y.pullback σ₂)) = ((Q.val.app _ (σ₁, label) (X, Y)).pullback σ₂) :=
  Q.val.naturality_apply σ₂.op (σ₁, label) (X, Y)

def IsIdempotent (Q : DependentOperator Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (X Y : Domain Γ₁),
    Q.val.app _ (σ.op, label) (X, (Q.val.app _ (σ.op, label) (X, Y))) = Q.val.app _ (σ.op, label) (X, Y)

theorem IsIdempotent.pullback {Q : DependentOperator Γ} (hQ : Q.IsIdempotent)
    (σ : Γ₁ ⟶ Γ) : IsIdempotent (Q.pullback σ) :=
  fun σ₁ ↦ hQ (σ₁ ≫ σ)

noncomputable def arrowAction (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (F : Domain Γ) : IdealAction Γ where
  val.app _ := fun (⟨σ⟩, label) => Preord.ofHom {
    toFun X := Q.val.app _ (σ.op, label) (P.val.app _ σ.op X,
      application (F.pullback σ) label (P.val.app _ σ.op X))
    monotone' := (Q.val.app _ (σ.op, label)).hom.monotone.comp
      ((monotone_id.prodMk (@application_mono_right _ (F.pullback σ) label)).comp
        (P.val.app _ σ.op).hom.monotone) }
  val.naturality σ₁ := fun (⟨σ⟩, label) => Preord.ext fun X => by
    have h := Q.app_pullback σ.op σ₁.unop label (P.val.app _ σ.op X)
      (application (F.pullback σ) label (P.val.app _ σ.op X))
    rw [pullback_application, ← P.app_pullback, ΩIdeal.pullback_pullback] at h
    exact h
  property := by
    intro Γ₁ ⟨⟨σ⟩, label⟩
    have ⟨h₁, h₂⟩ := Q.property
    have hP := P.property Γ₁ σ.op
    have hmP := (P.val.app Γ₁ σ.op).hom.monotone
    have hmApp : Monotone (application (F.pullback σ) label) :=
      fun _ _ h => application_mono_right _ _ h
    exact ΩIdeal.IsFinitary.comp₂ (Q.val.app Γ₁ (σ.op, label)).hom.monotone
      (fun Y X => h₁ σ label X Y) (h₂ σ label) hP
      ((application_argument_finitary _ label).comp hP hmApp)
      hmP (hmApp.comp hmP)

theorem pullback_arrowAction (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (F : Domain Γ) (σ : Γ₁ ⟶ Γ) :
    (Q.arrowAction P F).pullback σ =
      arrowAction (Q.pullback σ) (P.pullback σ) (F.pullback σ) := by
  ext Γ₂ ⟨⟨σ₁⟩, label⟩ X
  exact congrArg (fun H => Q.val.app _ (σ.op ≫ σ₁.op, label)
    (P.val.app _ (σ.op ≫ σ₁.op) X, application H label (P.val.app _ (σ.op ≫ σ₁.op) X)))
    (ΩIdeal.pullback_pullback F σ σ₁).symm

theorem arrowAction_mono (Q : DependentOperator Γ) (P : IdealOperator Γ)
    {F G : Domain Γ} (h : F ≤ G)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    (Q.arrowAction P F).val.app _ (σ.op, label) X ≤ (Q.arrowAction P G).val.app _ (σ.op, label) X :=
  (Q.val.app _ (σ.op, label)).hom.monotone (Prod.mk_le_mk.mpr ⟨fun _ _ h => h, application_mono_left (ΩIdeal.pullback_mono h σ) label _⟩)

theorem arrowAction_function_finitary (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (F : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A)
    (X : Domain Γ) {z : CoherentShape Γ}
    (hz : ((Q.arrowAction P F).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) z) :
    ∃ f, F.mem (𝟙 Γ) f ∧
      ((Q.arrowAction P (principalIdeal f)).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) z := by
  change (Q.val.app _ ((𝟙 Γ).op, label)
    (P.val.app _ (𝟙 Γ).op X, application (F.pullback (𝟙 Γ)) label _)).mem (𝟙 Γ) z at hz
  simp at hz
  have ⟨_, h₂⟩ := Q.property
  have ⟨y, hy, hz⟩ := h₂ (𝟙 Γ) label _ _ hz
  have ⟨f, hf, hy⟩ := application_function_finitary F label hy
  refine ⟨f, hf, ?_⟩
  change (Q.val.app _ ((𝟙 Γ).op, label)
    (P.val.app _ (𝟙 Γ).op X, application ((principalIdeal f).pullback (𝟙 Γ)) label _)).mem (𝟙 Γ) z
  simp
  exact (Q.val.app _ ((𝟙 Γ).op, label)).hom.monotone
    (Prod.mk_le_mk.mpr ⟨fun _ _ h => h, ΩLower.principal_le_iff.mpr hy⟩) _ _ hz

noncomputable def arrow (Q : DependentOperator Γ) (P : IdealOperator Γ) : IdealOperator Γ where
  val.app _ σ₁ := Preord.ofHom {
    toFun F := IdealAction.abstraction
      (arrowAction (Q.pullback σ₁.unop) (P.pullback σ₁.unop) F)
    monotone' _ _ h := IdealAction.abstraction_mono fun σ₂ label X =>
      arrowAction_mono (Q.pullback σ₁.unop) (P.pullback σ₁.unop) h σ₂ label X }
  val.naturality σ₂ σ₁ := Preord.ext fun F => by
    change IdealAction.abstraction (arrowAction (Q.pullback (σ₂.unop ≫ σ₁.unop))
      (P.pullback (σ₂.unop ≫ σ₁.unop)) (F.pullback σ₂.unop)) =
      ((IdealAction.abstraction (arrowAction (Q.pullback σ₁.unop)
        (P.pullback σ₁.unop) F)).pullback σ₂.unop)
    symm
    refine (pullback_abstraction _ σ₂.unop).trans ?_
    rw [pullback_arrowAction, DependentOperator.pullback_pullback, IdealOperator.pullback_pullback]
  property := fun _ ⟨σ₁⟩ => IdealAction.abstraction_finitary
    (arrowAction (Q.pullback σ₁) (P.pullback σ₁))
    (fun h label X => arrowAction_mono (Q.pullback σ₁) (P.pullback σ₁) h (𝟙 _) label X)
    (arrowAction_function_finitary (Q.pullback σ₁) (P.pullback σ₁))

theorem pullback_arrow (Q : DependentOperator Γ) (P : IdealOperator Γ) (σ : Γ₁ ⟶ Γ) :
    (Q.arrow P).pullback σ =
      arrow (Q.pullback σ) (P.pullback σ) := by
  ext Γ₂ ⟨σ₁⟩ F
  change IdealAction.abstraction (arrowAction (Q.pullback (σ₁ ≫ σ))
    (P.pullback (σ₁ ≫ σ)) F) =
      IdealAction.abstraction (arrowAction ((Q.pullback σ).pullback σ₁)
        ((P.pullback σ).pullback σ₁) F)
  rw [DependentOperator.pullback_pullback, IdealOperator.pullback_pullback]

theorem application_arrow (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (σ : Γ₁ ⟶ Γ) (F X : Domain Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) :
    application ((Q.arrow P).val.app _ σ.op F) label X =
      Q.val.app _ (σ.op, label) ((P.val.app _ σ.op X), (application F label (P.val.app _ σ.op X))) := by
  change application (IdealAction.abstraction (arrowAction (Q.pullback σ)
    (P.pullback σ) F)) label X = _
  rw [IdealAction.application_abstraction]
  change Q.val.app _ ((𝟙 Γ₁ ≫ σ).op, label) ((P.val.app _ (𝟙 Γ₁ ≫ σ).op X), (application (F.pullback (𝟙 Γ₁)) label (P.val.app _ (𝟙 Γ₁ ≫ σ).op X))) = _
  simp

theorem application_abstraction_arrowAction (Q : DependentOperator Γ)
    (P : IdealOperator Γ) (F : Domain Γ)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    application ((IdealAction.abstraction (Q.arrowAction P F)).pullback σ) label X =
      Q.val.app _ (σ.op, label) ((P.val.app _ σ.op X), (application (F.pullback σ) label (P.val.app _ σ.op X))) := by
  rw [pullback_abstraction, IdealAction.application_abstraction]
  change Q.val.app _ ((𝟙 Γ₁ ≫ σ).op, label) ((P.val.app _ (𝟙 Γ₁ ≫ σ).op X), (application (F.pullback (𝟙 Γ₁ ≫ σ)) label (P.val.app _ (𝟙 Γ₁ ≫ σ).op X))) = _
  simp

theorem arrowAction_abstraction (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (hP : P.IsIdempotent) (hQ : Q.IsIdempotent) (F : Domain Γ) :
    Q.arrowAction P (IdealAction.abstraction (Q.arrowAction P F)) = Q.arrowAction P F := by
  ext Γ₁ ⟨⟨σ⟩, label⟩ X
  change Q.val.app _ (σ.op, label) ((P.val.app _ σ.op X), (application ((IdealAction.abstraction (Q.arrowAction P F)).pullback σ)
      label (P.val.app _ σ.op X))) = _
  rw [application_abstraction_arrowAction, hP σ X, hQ σ label]
  rfl

theorem isIdempotent_arrow (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (hP : P.IsIdempotent) (hQ : Q.IsIdempotent) : (Q.arrow P).IsIdempotent := by
  intro Γ₁ σ F
  change IdealAction.abstraction (arrowAction (Q.pullback σ) (P.pullback σ)
    (IdealAction.abstraction (arrowAction (Q.pullback σ) (P.pullback σ) F))) = _
  rw [arrowAction_abstraction _ _ (hP.pullback σ) (hQ.pullback σ)]
  rfl

@[simp]
theorem arrow_value_id (Q : DependentOperator Γ) (P : IdealOperator Γ)
    (F : Domain Γ) :
    (Q.arrow P).val.app _ (𝟙 Γ).op F = IdealAction.abstraction (Q.arrowAction P F) := by
  change IdealAction.abstraction (arrowAction (Q.pullback (𝟙 Γ)) (P.pullback (𝟙 Γ)) F) = _
  rw [DependentOperator.pullback_id, IdealOperator.pullback_id]

theorem arrow_mono {Q Q' : DependentOperator Γ} {P P' : IdealOperator Γ}
    (hP : P ≤ P')
    (hQ : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
      (X Y : Domain Γ₁), Q.val.app _ (σ.op, label) (X, Y) ≤ Q'.val.app _ (σ.op, label) (X, Y)) :
    Q.arrow P ≤ Q'.arrow P' := by
  intro Γ₂ ⟨σ⟩ F
  apply IdealAction.abstraction_mono
  intro Γ₃ σ₂ label X Γ₄ σ₃ z hz
  exact hQ (σ₂ ≫ σ) label _ _ σ₃ z
    ((Q.val.app _ ((σ₂ ≫ σ).op, label)).hom.monotone
      ⟨hP _ (σ₂ ≫ σ).op X, application_mono_right _ label (hP _ (σ₂ ≫ σ).op X)⟩ σ₃ z hz)

theorem application_fixed (Q : DependentOperator Γ) (P : IdealOperator Γ)
    {F : Domain Γ} (hF : (Q.arrow P).val.app _ (𝟙 Γ).op F = F)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁)
    (hX : P.val.app _ σ.op X = X) :
    Q.val.app _ (σ.op, label) (X, (application (F.pullback σ) label X)) =
      application (F.pullback σ) label X := by
  have hFσ := congrArg (fun I : Domain Γ ↦ I.pullback σ) hF
  change ((Q.arrow P).val.app _ (𝟙 Γ).op F).pullback σ = (F.pullback σ) at hFσ
  rw [← (Q.arrow P).app_pullback, op_id, Category.id_comp] at hFσ
  simpa [hFσ, hX] using (Q.application_arrow P σ (F.pullback σ) X label).symm

end DependentOperator

end DomainSemantics.CoherentShape
