/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.CodeExtension

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

namespace CodeAssignment

noncomputable def resultOperator (F : CodeAssignment) (B : IdealAction Γ) : DependentOperator Γ where
  val.app _ p := Preord.ofHom {
    toFun | (X, Y) => F.extend (B.val.app _ p X) Y
    monotone' _ _ := fun ⟨hX, hY⟩ => ΩIdeal.bind₂_mono ((B.val.app _ p).hom.monotone hX) hY _ }
  val.naturality σ₁ p := Preord.ext fun (X, Y) =>
    (congrArg (fun T => F.extend T (Y.pullback σ₁.unop))
      (B.val.naturality_apply σ₁ p X)).trans
        (F.pullback_extend _ _ σ₁.unop).symm
  property := by
    constructor
    · intro Γ₂ σ label X Y
      exact (F.extend_finitary_left Y).comp (B.property _ (σ.op, label))
        (fun _ _ h => F.extend_mono_left h Y) X
    · intro Γ₂ σ label X
      exact F.extend_finitary_right (B.val.app _ (σ.op, label) X)

theorem pullback_resultOperator (F : CodeAssignment) (B : IdealAction Γ) (σ : Γ₁ ⟶ Γ) :
    (F.resultOperator B).pullback σ = F.resultOperator (B.pullback σ) :=
  rfl

noncomputable def piOperator (F : CodeAssignment) (A : Domain Γ)
    (B : IdealAction Γ) : IdealOperator Γ :=
  (F.resultOperator B).arrow (F.decode A)

theorem application_piOperator (F : CodeAssignment)
    (A : Domain Γ) (B : IdealAction Γ)
    (σ : Γ₁ ⟶ Γ) (G X : Domain Γ₁) (label : Σ A : Ty Γ₁, Tm Γ₁ A) :
    application ((F.piOperator A B).val.app _ σ.op G) label X =
      F.extend (B.val.app _ (σ.op, label) (F.extend (A.pullback σ) X))
        (application G label (F.extend (A.pullback σ) X)) :=
  (F.resultOperator B).application_arrow (F.decode A) σ G X label

theorem pullback_piOperator (F : CodeAssignment) (A : Domain Γ)
    (B : IdealAction Γ) (σ : Γ₁ ⟶ Γ) :
    (F.piOperator A B).pullback σ = F.piOperator (A.pullback σ) (B.pullback σ) := by
  rw [piOperator, DependentOperator.pullback_arrow, pullback_resultOperator, pullback_decode]
  rfl

theorem piOperator_mono (F : CodeAssignment)
    {A A' : Domain Γ} (hA : A ≤ A') {B B' : IdealAction Γ}
    (hB : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
      (X : Domain Γ₁), B.val.app _ (σ.op, label) X ≤ B'.val.app _ (σ.op, label) X) :
    F.piOperator A B ≤ F.piOperator A' B' := by
  apply DependentOperator.arrow_mono
  · exact fun _ ⟨σ₁⟩ => F.extend_mono_left (ΩIdeal.pullback_mono hA σ₁)
  · intro Γ₁ σ label X Y
    exact F.extend_mono_left (hB σ label X) Y

theorem resultOperator_isIdempotent {F : CodeAssignment} (hF : F.IsIdempotent)
    (B : IdealAction Γ) : (F.resultOperator B).IsIdempotent :=
  fun σ label X ↦ F.extend_idempotent hF (B.val.app _ (σ.op, label) X)

theorem piOperator_isIdempotent {F : CodeAssignment} (hF : F.IsIdempotent)
    (A : Domain Γ) (B : IdealAction Γ) : (F.piOperator A B).IsIdempotent :=
  DependentOperator.isIdempotent_arrow _ _
    (F.decode_isIdempotent hF A) (resultOperator_isIdempotent hF B)

end CodeAssignment

noncomputable def graphAction (f : CoherentGraph Γ) : IdealAction Γ :=
  IdealOperator.identity.branchAction (principalIdeal f.lamGenerator)

@[simp]
theorem graphAction_value (f : CoherentGraph Γ) (σ : Γ₁ ⟶ Γ)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    (graphAction f).val.app _ (σ.op, label) X =
      application (principalIdeal (f.reindex σ).lamGenerator) label X :=
  congrArg (fun I => application I label X)
    (ΩIdeal.presheaf_map_principal (R := pointedOrder) f.lamGenerator σ)

theorem pullback_graphAction (f : CoherentGraph Γ) (σ : Γ₁ ⟶ Γ) :
    (graphAction f).pullback σ = graphAction (f.reindex σ) := by
  ext Γ₂ ⟨⟨σ₁⟩, label⟩ X
  change application ((principalIdeal f.lamGenerator).pullback (σ₁ ≫ σ)) label X =
    application ((principalIdeal (f.reindex σ).lamGenerator).pullback σ₁) label X
  rw [← ΩIdeal.pullback_pullback, ΩIdeal.presheaf_map_principal]
  rfl

theorem graphAction_mono {f g : CoherentGraph Γ}
    (h : principalIdeal f.lamGenerator ≤ principalIdeal g.lamGenerator)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    (graphAction f).val.app _ (σ.op, label) X ≤ (graphAction g).val.app _ (σ.op, label) X :=
  application_mono_left (ΩIdeal.pullback_mono h σ) label X

theorem graphAction_le_of_valid (B : IdealAction Γ) (f : CoherentGraph Γ)
    (hf : IdealAction.GraphValid B (𝟙 Γ) f) (σ : Γ₁ ⟶ Γ)
    (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    (graphAction f).val.app _ (σ.op, label) X ≤ B.val.app _ (σ.op, label) X := by
  have hgraph : (IdealAction.abstraction B).mem (𝟙 Γ) f.lamGenerator :=
    (IdealAction.mem_abstraction _ _ _).mpr ⟨f, hf, le_rfl⟩
  have hle : application ((principalIdeal f.lamGenerator).pullback σ) label X ≤
      application ((IdealAction.abstraction B).pullback σ) label X :=
    application_mono_left
      (ΩIdeal.pullback_mono (ΩLower.principal_le_iff.mpr hgraph) σ) label X
  rw [pullback_abstraction, IdealAction.application_abstraction] at hle
  intro Γ₂ σ₁ z hz
  have h := hle σ₁ z hz
  change (B.val.app _ (σ.op ≫ (𝟙 Γ₁).op, label) X).mem σ₁ z at h
  simpa using h

namespace CodeAssignment

noncomputable def piGeneratorOperator (F : CodeAssignment) (a : CoherentShape Γ) (f : CoherentGraph Γ) :
    IdealOperator Γ :=
  F.piOperator (principalIdeal a) (graphAction f)

theorem pullback_piGeneratorOperator (F : CodeAssignment) (a : CoherentShape Γ) (f : CoherentGraph Γ)
    (σ : Γ₁ ⟶ Γ) :
    (F.piGeneratorOperator a f).pullback σ =
      F.piGeneratorOperator (reindex σ a) (f.reindex σ) := by
  unfold piGeneratorOperator
  rw [pullback_piOperator, ΩIdeal.presheaf_map_principal, pointedOrder_map,
    pullback_graphAction]
  rfl

theorem piGeneratorOperator_mono (F : CodeAssignment) {a a' : CoherentShape Γ}
    {f f' : CoherentGraph Γ} (ha : principalIdeal a ≤ principalIdeal a')
    (hf : principalIdeal f.lamGenerator ≤ principalIdeal f'.lamGenerator) :
    F.piGeneratorOperator a f ≤ F.piGeneratorOperator a' f' :=
  F.piOperator_mono ha (graphAction_mono hf)

theorem piGeneratorOperator_mono_components (F : CodeAssignment) {a a' : CoherentShape Γ}
    {f f' : CoherentGraph Γ} (ha : a ≤ a') (hf : f.1 ≤ f'.1) :
    F.piGeneratorOperator a f ≤ F.piGeneratorOperator a' f' :=
  F.piGeneratorOperator_mono (principalIdeal_mono ha) (principalIdeal_mono (CoherentGraph.lamGenerator_le_iff.mpr hf))

theorem piGeneratorOperator_isIdempotent {F : CodeAssignment} (hF : F.IsIdempotent)
    (a : CoherentShape Γ) (f : CoherentGraph Γ) :
    (F.piGeneratorOperator a f).IsIdempotent :=
  piOperator_isIdempotent hF _ _

end CodeAssignment

end DomainSemantics.CoherentShape
