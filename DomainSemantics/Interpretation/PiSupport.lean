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

variable {Γ Γ₁ Γ₂ : Ctx}

namespace CodeAssignment

theorem piLimit_rawExtend_rawPi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (T : Domain Γ)
    (B : RawAction Γ) (hB : B.IsFinitary) (hD : B.IsIdealValued)
    (F : Domain Γ) :
    piLimit.rawExtend (rawPi label T.val B) F.val =
      ((piLimit.piOperator T (B.toIdealAction hB hD)).val.app _ (𝟙 Γ).op F).val := by
  rw [rawPi_toIdealAction, piLimit.rawExtend_toLower, piLimit_extend_pi label]

theorem piOperator_fixed_of_rawExtend_rawPi (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (T : Domain Γ) (B : RawAction Γ)
    (hB : B.IsFinitary) (hD : B.IsIdealValued)
    {F : Domain Γ}
    (hF : piLimit.rawExtend (rawPi label T.val B) F.val = F.val) :
    (piLimit.piOperator T (B.toIdealAction hB hD)).val.app _ (𝟙 Γ).op F = F := by
  rw [piLimit_rawExtend_rawPi label T B hB hD F] at hF
  exact Subtype.val_injective hF

theorem application_piOperator_fixed (D : CodeAssignment)
    (T : Domain Γ) (B : IdealAction Γ)
    {F : Domain Γ}
    (hF : (D.piOperator T B).val.app _ (𝟙 Γ).op F = F)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    application (F.pullback σ) label X =
      D.extend (B.val.app _ (σ.op, label) (D.extend (T.pullback σ) X))
        (application (F.pullback σ) label (D.extend (T.pullback σ) X)) := by
  have hFσ := congrArg (fun I : Domain Γ ↦ I.pullback σ) hF
  rw [← (D.piOperator T B).app_pullback, op_id, Category.id_comp] at hFσ
  simpa [hFσ] using D.application_piOperator T B σ (F.pullback σ) X label

end CodeAssignment

namespace RawFamily

open CodeAssignment

variable {A : Term} {u : Bool}
variable (hA : Γ.as.terms ⊢ A : .sort u)
  (label : Σ A : Ty Γ, Ty (Γ.extend A))
  (C : RawFamily Γ) {B : RawFamily (Ctx.extension Γ hA)} (hB : B.IsFinitary)
  (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hC : (C.app _ σ.op ρ).IsDirected)
  (hD : (normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B σ ρ).IsIdealValued)
  {F : Domain Γ₁}
  (hF : piLimit.rawExtend ((pi piLimit (Ctx.rawDisplay hA) label C B).app _ σ.op ρ) F.val = F.val)
include hB hC hD hF

theorem application_rawPi_fixed (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
    (X : Domain Γ₂)
    (hX : piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) X.val = X.val) :
    piLimit.rawExtend (sectionValue (Ctx.rawDisplay hA) B (σ₁ ≫ σ) (ρ.pullback σ₁) name X.val)
        (CoherentShape.application (F.pullback σ₁) name X).val =
      (CoherentShape.application (F.pullback σ₁) name X).val := by
  let T : Domain Γ₁ := (C.app _ σ.op ρ).toIdeal hC
  let U : RawAction Γ₁ := normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B σ ρ
  have hU : U.IsFinitary := normalizedBodyAction_isFinitary piLimit (Ctx.rawDisplay hA) C hB σ ρ
  let V : IdealAction Γ₁ := U.toIdealAction hU hD
  have hF' : (piLimit.piOperator T V).val.app _ (𝟙 Γ₁).op F = F :=
    piOperator_fixed_of_rawExtend_rawPi (Ty.pairPresheaf.map σ.op label) T U hU hD hF
  have hdomain : (T.pullback σ₁).val = C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁) :=
    (C.app_pullback σ.op σ₁ ρ)
  have hXraw : (piLimit.extend (T.pullback σ₁) X).val = X.val := by
    rw [← piLimit.rawExtend_toLower, hdomain]
    exact hX
  have hX' : (piLimit.decode T).val.app _ σ₁.op X = X :=
    Subtype.val_injective hXraw
  let Y : Domain Γ₂ := CoherentShape.application (F.pullback σ₁) name X
  have hresult : piLimit.extend (V.val.app _ (σ₁.op, name) X) Y = Y :=
    (piLimit.resultOperator V).application_fixed (piLimit.decode T) hF' σ₁ name X hX'
  have hcode : (V.val.app _ (σ₁.op, name) X).val =
      sectionValue (Ctx.rawDisplay hA) B (σ₁ ≫ σ) (ρ.pullback σ₁) name X.val := by
    rw [RawAction.toIdealAction_value_toLower]
    change normalizedSectionValue piLimit (Ctx.rawDisplay hA) C B (σ₁ ≫ σ) (ρ.pullback σ₁) name X.val = _
    rw [normalizedSectionValue, hX]
  calc
    piLimit.rawExtend (sectionValue (Ctx.rawDisplay hA) B (σ₁ ≫ σ) (ρ.pullback σ₁) name X.val)
        Y.val = piLimit.rawExtend (V.val.app _ (σ₁.op, name) X).val Y.val :=
      congrArg (fun T : RawValue Γ₂ ↦ piLimit.rawExtend T Y.val) hcode.symm
    _ = (piLimit.extend (V.val.app _ (σ₁.op, name) X) Y).val :=
      piLimit.rawExtend_toLower (V.val.app _ (σ₁.op, name) X) Y
    _ = Y.val := congrArg Subtype.val hresult

theorem application_rawPi_fixed_support (σ₁ : Γ₂ ⟶ Γ₁) (name : Σ A : Ty Γ₂, Tm Γ₂ A)
    (X : Domain Γ₂)
    {y : CoherentShape Γ₂}
    (hy : (CoherentShape.application (F.pullback σ₁) name X).mem (𝟙 Γ₂) y)
    (hne : ¬ y ≤ ⊥) :
    Nonempty (Raw.ContextSection hA (σ₁ ≫ σ) name) := by
  let T := (C.app _ σ.op ρ).toIdeal hC
  let U := normalizedBodyAction piLimit (Ctx.rawDisplay hA) C B σ ρ
  have hU : U.IsFinitary := normalizedBodyAction_isFinitary piLimit (Ctx.rawDisplay hA) C hB σ ρ
  let V := U.toIdealAction hU hD
  have hF' : (piLimit.piOperator T V).val.app _ (𝟙 Γ₁).op F = F :=
    piOperator_fixed_of_rawExtend_rawPi (Ty.pairPresheaf.map σ.op label) T U hU hD hF
  let J := piLimit.extend (T.pullback σ₁) X
  let Y := CoherentShape.application (F.pullback σ₁) name J
  have hβ := piLimit.application_piOperator_fixed T V hF' σ₁ name X
  have hy' : (piLimit.rawExtend (U.app _ (σ₁.op, name) J.val) Y.val).mem (𝟙 Γ₂) y := by
    change (piLimit.rawExtend (V.val.app _ (σ₁.op, name) J).val Y.val).mem (𝟙 Γ₂) y
    rw [piLimit.rawExtend_toLower]
    exact (congrArg (fun I : Domain Γ₂ ↦ I.mem (𝟙 Γ₂) y) hβ).mp hy
  exact piLimit_rawExtend_sectionValue_support (Ctx.rawDisplay hA) B (σ₁ ≫ σ) (ρ.pullback σ₁) name
    (piLimit.rawExtend (C.app _ (σ₁ ≫ σ).op (ρ.pullback σ₁)) J.val) Y.val hy' hne

theorem outputAtom_rawPi_fixed_support (σ₁ : Γ₂ ⟶ Γ₁) {name : Σ A : Ty Γ₂, Tm Γ₂ A}
    {x y : CoherentShape Γ₂}
    (hy : OutputAtom (F.pullback σ₁).val name x y)
    (hne : ¬ y ≤ ⊥) :
    Nonempty (Raw.ContextSection hA (σ₁ ≫ σ) name) := by
  apply application_rawPi_fixed_support hA label C hB σ ρ hC hD hF
    σ₁ name (principalIdeal x) _ hne
  exact hy.mem_application ((principalIdeal_mem x (𝟙 Γ₂) x).mpr
    (by simp))

end RawFamily

end DomainSemantics.CoherentShape
