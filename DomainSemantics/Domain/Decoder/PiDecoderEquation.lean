/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Domain.Pi
import DomainSemantics.Domain.Decoder.PiSupport

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}
variable (F : CodeAssignment)

namespace CodeAssignment

theorem mem_extend_piStep_pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : Domain Γ)
    (B : IdealAction Γ) (G : Domain Γ) (y : CoherentShape Γ) :
    (F.piStep.extend (pi label A B) G).mem (𝟙 Γ) y ↔
      ((F.piOperator A B).val.app _ (𝟙 Γ).op G).mem (𝟙 Γ) y := by
  rw [mem_extend]
  constructor
  · intro ⟨c, hc, hy⟩
    have ⟨a, f, ha, hf, hc⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hc
    simp at hc
    simp at hy
    have hy' := F.piStep.eval_mono_code hc G (𝟙 Γ) y hy
    exact F.piOperator_mono (ΩLower.principal_le_iff.mpr ha)
      (graphAction_le_of_valid B f hf) _ (𝟙 Γ).op G (𝟙 Γ) y hy'
  · intro hy
    have ⟨a, ha, hy⟩ := F.piOperator_domain_finitary A B G hy
    rw [← branchAction_abstraction B] at hy
    have ⟨h, hh, hy⟩ := F.piOperator_body_finitary (principalIdeal a)
      (IdealAction.abstraction B) G hy
    have ⟨f, hf, hhf⟩ := (IdealAction.mem_abstraction _ _ _).mp hh
    have hbody : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
        (X : Domain Γ₁),
        (IdealOperator.identity.branchAction (principalIdeal h)).val.app _ (σ.op, label) X ≤
          (graphAction f).val.app _ (σ.op, label) X :=
      fun σ label X => application_mono_left (ΩIdeal.pullback_mono (ΩLower.principal_mono hhf) σ) label X
    have hyf : ((F.piOperator (principalIdeal a) (graphAction f)).val.app _ (𝟙 Γ).op G).mem
        (𝟙 Γ) y :=
      F.piOperator_mono (fun _ _ h ↦ h) hbody _ (𝟙 Γ).op G (𝟙 Γ) y hy
    refine ⟨piGenerator label a f, ?_, ?_⟩
    · apply (BasisAction.mem_pi _ _ _ _ _).mpr
      exact ⟨a, f, ha, hf, by simp⟩
    · simp
      exact hyf

theorem piOperator_value_pullback
    (A : Domain Γ) (B : IdealAction Γ)
    (G : Domain Γ) (σ : Γ₁ ⟶ Γ) :
    ((F.piOperator A B).val.app _ (𝟙 Γ).op G).pullback σ =
      (F.piOperator (A.pullback σ) (B.pullback σ)).val.app _ (𝟙 Γ₁).op (G.pullback σ) := by
  rw [← pullback_piOperator]
  change ((F.piOperator A B).val.app _ (𝟙 Γ).op G).pullback σ =
    (F.piOperator A B).val.app _ (𝟙 Γ₁ ≫ σ).op (G.pullback σ)
  rw [← (F.piOperator A B).app_pullback]
  simp

theorem extend_piStep_pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : Domain Γ)
    (B : IdealAction Γ) (G : Domain Γ) :
    F.piStep.extend (pi label A B) G = (F.piOperator A B).val.app _ (𝟙 Γ).op G := by
  ext Γ₁ σ y
  rw [← ΩIdeal.presheaf_map_mem_id, F.piStep.pullback_extend, pullback_pi,
    ← ΩIdeal.presheaf_map_mem_id _ σ y, piOperator_value_pullback]
  exact F.mem_extend_piStep_pi (Ty.pairPresheaf.map σ.op label) _ _ _ y

theorem decode_piStep_pi (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (A : Domain Γ) (B : IdealAction Γ) :
    F.piStep.decode (pi label A B) = F.piOperator A B := by
  ext ⟨Γ₁⟩ ⟨σ⟩ G
  change F.piStep.extend ((pi label A B).pullback σ) G = _
  rw [pullback_pi, F.extend_piStep_pi, ← F.pullback_piOperator]
  change (F.piOperator A B).val.app _ (𝟙 Γ₁ ≫ σ).op G = (F.piOperator A B).val.app _ σ.op G
  simp

end CodeAssignment

end DomainSemantics.CoherentShape
