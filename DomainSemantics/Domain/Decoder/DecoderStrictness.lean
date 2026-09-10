/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

@[simp]
theorem bottomIdeal_mem (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (bottomIdeal Γ).mem σ y ↔ y ≤ ⊥ := by
  change (ΩIdeal.principal pointedOrder ⊥).mem σ y ↔ y ≤ ⊥
  simp

theorem application_bottomIdeal (label : Σ A : Ty Γ, Tm Γ A) (X : Domain Γ) :
    application (bottomIdeal Γ) label X = bottomIdeal Γ := by
  apply le_antisymm
  · intro Γ₁ σ y hy
    have ⟨x, _, hy⟩ := (CoherentShape.mem_application _ _ _ _ _).mp hy
    apply (bottomIdeal_mem σ y).mpr
    apply hy.le_of_outputAtom
    rintro w ⟨f, i, hf, _, _, rfl⟩
    rw [pullback_bottomIdeal, ΩIdeal.val_mem, bottomIdeal_mem] at hf
    exact le_bot_iff.mpr (CoherentGraph.lamGenerator_le_bot_iff.mp hf i)
  · exact IdealOperator.bottomIdeal_le _

theorem IdealAction.abstraction_eq_bottom (B : IdealAction Γ)
    (hB : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
      (X : Domain Γ₁), B.val.app _ (σ.op, label) X = bottomIdeal Γ₁) :
    B.abstraction = bottomIdeal Γ := by
  apply le_antisymm
  · intro Γ₁ σ y hy
    have ⟨⟨f, hcoh⟩, hf, hy⟩ := (IdealAction.mem_abstraction _ _ _).mp hy
    have houtputs : f.IsBottom := by
      intro i
      have h := hf i
      change (B.val.app _ (σ.op, f.names i) (principalIdeal (CoherentGraph.input ⟨f, hcoh⟩ i))).mem
        (𝟙 Γ₁) (CoherentGraph.output ⟨f, hcoh⟩ i) at h
      rw [hB, bottomIdeal_mem] at h
      exact le_bot_iff.mp h
    exact (bottomIdeal_mem σ y).mpr (hy.trans (CoherentGraph.lamGenerator_le_bot_iff.mpr houtputs))
  · exact IdealOperator.bottomIdeal_le _

def IdealOperator.IsStrict (P : IdealOperator Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ), P.val.app _ σ.op (bottomIdeal Γ₁) = bottomIdeal Γ₁

theorem IdealOperator.isStrict_bottom : (bottom : IdealOperator Γ).IsStrict := fun _ ↦ rfl

namespace CodeAssignment

theorem rawExtend_nonbottom_code (F : CodeAssignment)
    (hF : ∀ {Γ : Ctx}, F.app _ (⊥ : CoherentShape Γ) = IdealOperator.bottom)
    {T I : RawValue Γ} {σ : Γ₁ ⟶ Γ} {y : CoherentShape Γ₁}
    (hy : (F.rawExtend T I).mem σ y) (hne : ¬ y ≤ ⊥) :
    ∃ c, T.mem σ c ∧ ¬ c ≤ ⊥ := by
  have ⟨c, hc, x, _, hy⟩ := (mem_rawExtend _ _ _ _ _).mp hy
  refine ⟨c, hc, fun hbot => hne ?_⟩
  have hy' := F.eval_mono_code hbot (principalIdeal x) (𝟙 Γ₁) y hy
  change ((F.app _ (⊥ : CoherentShape Γ₁)).val.app _ (𝟙 Γ₁).op
    (principalIdeal x)).mem (𝟙 Γ₁) y at hy'
  rw [hF] at hy'
  exact (bottomIdeal_mem _ _).mp hy'

def IsPayloadStrict (F : CodeAssignment) : Prop :=
  ∀ {Γ : Ctx} (a : CoherentShape Γ), IdealOperator.IsStrict (F.app _ a)

theorem rawExtend_bottom_payload {F : CodeAssignment} (hF : F.IsPayloadStrict)
    (T : RawValue Γ) : F.rawExtend T ⊥ = ⊥ := by
  apply le_antisymm
  · intro Γ₁ σ y
    simp_rw [mem_rawExtend]
    intro ⟨c, _, x, hx, hy⟩
    have hy' := F.eval_mono_payload c (Y := bottomIdeal Γ₁)
      (ΩLower.principal_mono hx) (𝟙 Γ₁) y hy
    change ((F.app _ c).val.app _ (𝟙 Γ₁).op (bottomIdeal Γ₁)).mem (𝟙 Γ₁) y at hy'
    rw [hF c, bottomIdeal_mem] at hy'
    exact hy'
  · intro Γ₁ σ y hy
    exact (F.rawExtend T ⊥).lower σ ((ΩLower.mem_bot _ _).mp hy) ((F.rawExtend T ⊥).bottom σ)

theorem extend_bottom_payload {F : CodeAssignment} (hF : F.IsPayloadStrict)
    (T : Domain Γ) : F.extend T (bottomIdeal Γ) = bottomIdeal Γ := by
  rw [bottomIdeal_eq_bot]
  exact Subtype.val_injective (F.rawExtend_bottom_payload hF T.val)

theorem piOperator_isStrict {F : CodeAssignment} (hF : F.IsPayloadStrict)
    (A : Domain Γ) (B : IdealAction Γ) :
    (F.piOperator A B).IsStrict := by
  intro Γ₁ σ
  apply IdealAction.abstraction_eq_bottom
  intro Γ₂ σ₁ label X
  change F.extend (B.val.app _ ((σ₁ ≫ σ).op, label) (F.extend (A.pullback (σ₁ ≫ σ)) X))
    (application ((bottomIdeal Γ₁).pullback σ₁) label
      (F.extend (A.pullback (σ₁ ≫ σ)) X)) = bottomIdeal Γ₂
  rw [pullback_bottomIdeal, application_bottomIdeal, extend_bottom_payload hF]

theorem piGeneratorOperator_isStrict {F : CodeAssignment} (hF : F.IsPayloadStrict)
    (a : CoherentShape Γ) (f : CoherentGraph Γ) :
    (F.piGeneratorOperator a f).IsStrict :=
  piOperator_isStrict hF _ _

theorem piStep_isPayloadStrict {F : CodeAssignment} (hF : F.IsPayloadStrict) :
    F.piStep.IsPayloadStrict := by
  intro Γ ⟨a, ha⟩ Γ₁ σ
  cases a with
  | sort r => exact universeIdeal_bottom r
  | forallE _ _ _ _ _ _ => exact piGeneratorOperator_isStrict hF _ _ σ
  | nat => exact natIdeal_bottom
  | _ => rfl

theorem piStage_isPayloadStrict (n : Nat) : (piStage n).IsPayloadStrict := by
  induction n with
  | zero => exact fun _ ↦ IdealOperator.isStrict_bottom
  | succ n ih => exact piStep_isPayloadStrict ih

theorem piLimit_isPayloadStrict : piLimit.IsPayloadStrict := by
  intro Γ₁ ⟨a, ha⟩
  rw [piLimit_app]
  exact fun {_} σ => piStage_isPayloadStrict (a.rank + 1) ⟨a, ha⟩ σ

end CodeAssignment

end DomainSemantics.CoherentShape
