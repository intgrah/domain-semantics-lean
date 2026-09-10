/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiDecoder

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ : Ctx}
variable (F : CodeAssignment) {z : CoherentShape Γ}

theorem branchAction_abstraction (B : IdealAction Γ) :
    IdealOperator.identity.branchAction (IdealAction.abstraction B) = B := by
  ext ⟨Γ₁⟩ ⟨⟨σ⟩, label⟩ X
  change application ((IdealAction.abstraction B).pullback σ) label X = _
  refine (congrArg (fun I => application I label X) (pullback_abstraction B σ)).trans ?_
  rw [IdealAction.application_abstraction]
  change B.val.app _ (σ.op ≫ (𝟙 Γ₁).op, label) X = _
  simp
  rfl

namespace CodeAssignment

noncomputable def piAction (A : Domain Γ)
    (B : IdealAction Γ) (G : Domain Γ) : IdealAction Γ :=
  (F.resultOperator B).arrowAction (F.decode A) G

theorem piAction_value_id (A : Domain Γ)
    (B : IdealAction Γ) (G X : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) :
    (F.piAction A B G).val.app _ ((𝟙 Γ).op, label) X =
      F.extend (B.val.app _ ((𝟙 Γ).op, label) (F.extend A X))
        (application G label (F.extend A X)) := by
  change F.extend (B.val.app _ ((𝟙 Γ).op, label) (F.extend (A.pullback (𝟙 Γ)) X))
    (application (G.pullback (𝟙 Γ)) label (F.extend (A.pullback (𝟙 Γ)) X)) = _
  simp

theorem piAction_mono_domain
    {A A' : Domain Γ} (hA : A ≤ A')
    (B : IdealAction Γ) (G X : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) :
    (F.piAction A B G).val.app _ ((𝟙 Γ).op, label) X ≤
      (F.piAction A' B G).val.app _ ((𝟙 Γ).op, label) X := by
  rw [piAction_value_id, piAction_value_id]
  intro Γ₁ σ y hy
  exact F.extend_mono_right (application_mono_right G label (F.extend_mono_left hA X))
    σ y (F.extend_mono_left ((B.val.app _ ((𝟙 Γ).op, label)).hom.monotone (F.extend_mono_left hA X)) _ σ y hy)

theorem piAction_domain_finitary
    (A : Domain Γ) (B : IdealAction Γ)
    (G X : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A)
    (hz : ((F.piAction A B G).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) z) :
    ∃ a, A.mem (𝟙 Γ) a ∧
      ((F.piAction (principalIdeal a) B G).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) z := by
  simp_rw [piAction_value_id] at hz ⊢
  have hmApp : Monotone (application G label) := fun _ _ h => application_mono_right _ _ h
  have hfin := ΩIdeal.IsFinitary.comp₂ (f := fun (T, Y) => F.extend T Y)
    (fun _ _ ⟨hT, hX⟩ => ΩIdeal.bind₂_mono hT hX F.evalStep)
    F.extend_finitary_left F.extend_finitary_right
    (B.property _ ((𝟙 Γ).op, label)) (application_argument_finitary G label)
    (B.val.app _ ((𝟙 Γ).op, label)).hom.monotone hmApp
  exact hfin.comp (F.extend_finitary_left X)
    (fun _ _ h => ΩIdeal.bind₂_mono ((B.val.app _ ((𝟙 Γ).op, label)).hom.monotone h)
      (hmApp h) F.evalStep) A hz

theorem piOperator_domain_finitary
    (A : Domain Γ) (B : IdealAction Γ)
    (G : Domain Γ)
    (hz : ((F.piOperator A B).val.app _ (𝟙 Γ).op G).mem (𝟙 Γ) z) :
    ∃ a, A.mem (𝟙 Γ) a ∧
      ((F.piOperator (principalIdeal a) B).val.app _ (𝟙 Γ).op G).mem (𝟙 Γ) z := by
  rw [piOperator, DependentOperator.arrow_value_id] at hz
  have ⟨a, ha, hz⟩ := IdealAction.abstraction_finitary (fun A ↦ F.piAction A B G)
    (fun h label X ↦ F.piAction_mono_domain h B G X label)
    (fun A label X _ hz ↦ F.piAction_domain_finitary A B G X label hz) A hz
  refine ⟨a, ha, ?_⟩
  rwa [piOperator, DependentOperator.arrow_value_id]

theorem piAction_mono_body
    (A : Domain Γ) {H H' : Domain Γ} (hH : H ≤ H')
    (G X : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) :
    (F.piAction A (IdealOperator.identity.branchAction H) G).val.app _ ((𝟙 Γ).op, label) X ≤
      (F.piAction A (IdealOperator.identity.branchAction H') G).val.app _ ((𝟙 Γ).op, label) X := by
  rw [piAction_value_id, piAction_value_id]
  change F.extend (application (H.pullback (𝟙 Γ)) label (F.extend A X)) _ ≤
    F.extend (application (H'.pullback (𝟙 Γ)) label (F.extend A X)) _
  exact F.extend_mono_left
    (application_mono_left (ΩIdeal.pullback_mono hH (𝟙 Γ)) label _) _

theorem piAction_body_finitary
    (A H G X : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A)
    (hz : ((F.piAction A (IdealOperator.identity.branchAction H) G).val.app _ ((𝟙 Γ).op, label) X).mem
      (𝟙 Γ) z) :
    ∃ h, H.mem (𝟙 Γ) h ∧
      ((F.piAction A (IdealOperator.identity.branchAction (principalIdeal h)) G).val.app _ ((𝟙 Γ).op, label) X).mem (𝟙 Γ) z := by
  rw [piAction_value_id] at hz
  change (F.extend (application (H.pullback (𝟙 Γ)) label (F.extend A X)) _).mem (𝟙 Γ) z at hz
  rw [ΩIdeal.pullback_id] at hz
  have ⟨b, hb, hz⟩ := F.extend_finitary_left _ _ hz
  have ⟨h, hh, hb⟩ := application_function_finitary H label hb
  refine ⟨h, hh, ?_⟩
  rw [piAction_value_id]
  change (F.extend (application ((principalIdeal h).pullback (𝟙 Γ)) label (F.extend A X)) _).mem
    (𝟙 Γ) z
  simpa using F.extend_mono_left (ΩLower.principal_le_iff.mpr hb) _ (𝟙 Γ) z hz

theorem piOperator_body_finitary
    (A H G : Domain Γ)
    (hz : ((F.piOperator A (IdealOperator.identity.branchAction H)).val.app _ (𝟙 Γ).op G).mem
      (𝟙 Γ) z) :
    ∃ h, H.mem (𝟙 Γ) h ∧
      ((F.piOperator A (IdealOperator.identity.branchAction (principalIdeal h))).val.app _ (𝟙 Γ).op G).mem (𝟙 Γ) z := by
  rw [piOperator, DependentOperator.arrow_value_id] at hz
  have ⟨h, hh, hz⟩ := IdealAction.abstraction_finitary
    (fun H ↦ F.piAction A (IdealOperator.identity.branchAction H) G)
    (fun h label X ↦ F.piAction_mono_body A h G X label)
    (fun H label X _ hz ↦ F.piAction_body_finitary A H G X label hz) H hz
  refine ⟨h, hh, ?_⟩
  rwa [piOperator, DependentOperator.arrow_value_id]

end CodeAssignment

end DomainSemantics.CoherentShape
