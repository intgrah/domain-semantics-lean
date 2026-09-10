/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Pi
public import DomainSemantics.Domain.Decoder.PiStages
import DomainSemantics.Domain.Decoder.PiFixedPoint
import DomainSemantics.Interpretation.BinderSupport

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory

variable {Γ Γ₁ : Ctx}

private theorem decodedArrowAction_value (D : CodeAssignment)
    (T : Domain Γ) (B : IdealAction Γ)
    (L : Domain Γ) (σ₁ : Γ₁ ⟶ Γ)
    (name : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    ((D.resultOperator B).arrowAction (D.decode T) L).val.app _ (σ₁.op, name) X =
      D.extend
        (B.val.app _ (σ₁.op, name)
          (D.extend (T.pullback σ₁) X))
        (CoherentShape.application (L.pullback σ₁)
          name (D.extend (T.pullback σ₁) X)) := rfl

namespace RawFamily

open CodeAssignment

variable {A : Term} {u : Bool}

private theorem normalizedBodyAction_value (D : CodeAssignment)
    (hA : Γ.as.terms ⊢ A : .sort u)
    (C : RawFamily Γ) (B : RawFamily (Ctx.extension Γ hA))
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁)
    (name : Σ A : Ty Γ₂, Tm Γ₂ A) (I : RawValue Γ₂) :
    (normalizedBodyAction D (Ctx.rawDisplay hA) C B σ ρ).app _ (σ₁.op, name) I =
      sectionValue (Ctx.rawDisplay hA) B (σ₁ ≫ σ) (ρ.pullback σ₁) name
        (D.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) I) := rfl

theorem normalizedAbstraction_fixed (hA : Γ.as.terms ⊢ A : .sort u)
    (C : RawFamily Γ) (B M : RawFamily (Ctx.extension Γ hA))
    (hBF : B.IsFinitary) (hMF : M.IsFinitary)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (label : Σ A : Ty Γ₁, Ty (Γ₁.extend A))
    (hC : (C.app _ σ.op ρ).IsDirected)
    (hBI : (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B σ ρ).IsIdealValued)
    (hMI : (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C M σ ρ).IsIdealValued)
    (hbody : ∀ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (J : Domain Γ₂),
      piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) J.val = J.val →
      piLimit.rawExtend
        (sectionValue (Ctx.rawDisplay hA) B (σ₁ ≫ σ) (ρ.pullback σ₁) name J.val)
        (sectionValue (Ctx.rawDisplay hA) M (σ₁ ≫ σ) (ρ.pullback σ₁) name J.val) =
        sectionValue (Ctx.rawDisplay hA) M (σ₁ ≫ σ) (ρ.pullback σ₁) name J.val) :
    piLimit.rawExtend
      (rawPi label (C.app _ σ.op ρ) (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B σ ρ))
      (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C M σ ρ).abstraction =
      (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C M σ ρ).abstraction := by
  let T := (C.app _ σ.op ρ).toIdeal hC
  let b := normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B σ ρ
  let m := normalizedBodyAction piLimit (Ctx.rawDisplay hA) C M σ ρ
  have hbF : b.IsFinitary := normalizedBodyAction_isFinitary piLimit (Ctx.rawDisplay hA) C hBF σ ρ
  have hmF : m.IsFinitary := normalizedBodyAction_isFinitary piLimit (Ctx.rawDisplay hA) C hMF σ ρ
  let L := m.abstraction.toIdeal (m.abstraction_isDirected hMI)
  have hdecode {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (J : Domain Γ₂) :
      piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) J.val =
        (piLimit.extend (T.pullback σ₁) J).val := by
    rw [op_comp, ← C.app_pullback]
    exact piLimit.rawExtend_toLower (T.pullback σ₁) J
  have hβ {Γ₂ : Ctx} (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
      (J : Domain Γ₂) :
      (CoherentShape.application (L.pullback σ₁) name J).val = m.app _ (σ₁.op, name) J.val := by
    rw [← rawApplication_singleton]
    change rawApplication (m.abstraction.pullback σ₁) {name} J.val = _
    have h := RawAction.rawApplication_abstraction_eq_value (m.pullback σ₁)
      (hmF.pullback σ₁) (hMI.pullback σ₁) J {name} name rfl
      (fun _ _ hname _ _ _ => Or.inr (by simpa using hname))
    rw [RawAction.pullback, RawAction.app_map] at h
    simpa only [RawAction.pullback_abstraction, RawAction.pullback, op_id, Category.comp_id] using h
  change piLimit.rawExtend (rawPi label T.val b) L.val = m.abstraction
  rw [rawPi_toIdealAction label T b hbF hBI, piLimit.rawExtend_toLower,
    piLimit_extend_pi label, piOperator, DependentOperator.arrow_value_id]
  symm
  apply m.abstraction_eq_of_ideal_values
  intro Γ₂ σ₁ name X
  rw [decodedArrowAction_value]
  let J := piLimit.extend (T.pullback σ₁) X
  have hJ : piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) J.val = J.val := by
    rw [hdecode, extend_idempotent piLimit_isIdempotent]
  rw [← piLimit.rawExtend_toLower, hβ, RawAction.toIdealAction_value_toLower,
    normalizedBodyAction_value, normalizedBodyAction_value, normalizedBodyAction_value,
    hJ, hbody σ₁ name J hJ, hdecode]

end RawFamily

end DomainSemantics.CoherentShape
