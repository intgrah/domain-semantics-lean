/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Interpretation
import DomainSemantics.Interpretation.Prop
import DomainSemantics.Interpretation.SourceQuery
import DomainSemantics.Interpretation.Witnesses

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory

variable {Γ Γ₁ : Ctx} {A a b : Term} {u : Bool}

theorem rawInterpret_beta_value (D : CodeAssignment)
    (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (hF : (RawFamily.normalizedBodyAction D (Ctx.rawDisplay hA) (rawInterpret D Γ A)
      (rawInterpret D (Ctx.extension Γ hA) b) σ ρ).IsIdealValued)
    (hX : ((rawInterpret D Γ a).app _ σ.op ρ).IsDirected) :
    (rawInterpret D Γ (.app (.lam A b) a)).app _ σ.op ρ =
      (rawInterpret D (Ctx.extension Γ hA) b).app _ (σ ≫ (Raw.ContextSection.ofTerm hA ha).hom).op
        (ρ.push (D.rawExtend ((rawInterpret D Γ A).app _ σ.op ρ)
          ((rawInterpret D Γ a).app _ σ.op ρ))) := by
  change (RawFamily.application (rawInterpret D Γ (.lam A b))
    (rawInterpret D Γ a) (RawFamily.sourceQuery Γ a)).app _ σ.op ρ = _
  rw [rawInterpret_lam D hA, RawFamily.application_value, RawFamily.abstraction_value]
  exact RawFamily.rawApplication_sourceQuery_abstraction_eq_body D hA ha
    (rawInterpret D Γ A) (rawInterpret_isFinitary D _ b) σ ρ hF
    (((rawInterpret D Γ a).app _ σ.op ρ).toIdeal hX)

theorem rawInterpret_beta (D : CodeAssignment)
    (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (hF : (RawFamily.normalizedBodyAction D (Ctx.rawDisplay hA) (rawInterpret D Γ A)
      (rawInterpret D (Ctx.extension Γ hA) b) σ ρ).IsIdealValued)
    (hX : ((rawInterpret D Γ a).app _ σ.op ρ).IsDirected)
    (iha : D.rawExtend ((rawInterpret D Γ A).app _ σ.op ρ)
      ((rawInterpret D Γ a).app _ σ.op ρ) = (rawInterpret D Γ a).app _ σ.op ρ)
    (ihb : (rawInterpret D (Ctx.extension Γ hA) b).app _ (σ ≫ (Raw.ContextSection.ofTerm hA ha).hom).op
        (ρ.push ((rawInterpret D Γ a).app _ σ.op ρ)) =
      (rawInterpret D Γ (b.subst (Subst.one a))).app _ σ.op ρ) :
    (rawInterpret D Γ (.app (.lam A b) a)).app _ σ.op ρ =
      (rawInterpret D Γ (b.subst (Subst.one a))).app _ σ.op ρ := by
  rw [rawInterpret_beta_value D hA ha σ ρ hF hX, iha]
  exact ihb

end DomainSemantics.CoherentShape

namespace DomainSemantics

open CategoryTheory

theorem Raw.ContextSection.ofTerm_hom_eq_of_defeq {Γ : Ctx} {A a b : Term} {u : Bool}
    (hA : Γ.as.terms ⊢ A : .sort u) (hab : Γ.as.terms ⊢ a ≡ b : A) :
    (ofTerm hA hab.hasType.1).hom = (ofTerm hA hab.hasType.2).hom :=
  (RawCtx.toCtx_map_eq_iff _ _).mpr (Raw.HomEq.one Γ.as.wf hA a b hab).typed

namespace CoherentShape

variable {Γ Γ₁ : Ctx} {A a b C x h : Term} {u : Bool}

theorem rawInterpret_tr_K (D : CodeAssignment)
    (hA : Γ.as.terms ⊢ A : .sort u) (hab : Γ.as.terms ⊢ a ≡ b : A)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (ihab : (rawInterpret D Γ a).app _ σ.op ρ =
      (rawInterpret D Γ b).app _ σ.op ρ)
    (ihC : (rawInterpret D (Ctx.extension Γ hA) C).app _ (σ ≫ (Raw.ContextSection.ofTerm hA hab.hasType.1).hom).op
        (ρ.push ((rawInterpret D Γ a).app _ σ.op ρ)) =
      (rawInterpret D Γ (C.subst (Subst.one a))).app _ σ.op ρ)
    (ihx : D.rawExtend
        ((rawInterpret D Γ (C.subst (Subst.one a))).app _ σ.op ρ)
        ((rawInterpret D Γ x).app _ σ.op ρ) =
      (rawInterpret D Γ x).app _ σ.op ρ) :
    (rawInterpret D Γ (.tr A a b C x h)).app _ σ.op ρ =
      (rawInterpret D Γ x).app _ σ.op ρ := by
  rw [rawInterpret_tr D hA hab.hasType.2, RawFamily.decode_app_hom_coe,
    RawFamily.instantiate_value,
    ← Raw.ContextSection.ofTerm_hom_eq_of_defeq hA hab, ← ihab, ihC]
  exact ihx

end CoherentShape

end DomainSemantics

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ Γ₁ : Ctx} {p h h' : Term}

theorem rawInterpret_proofIrrel (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁)
    (ihp : piLimit.rawExtend ((rawInterpret piLimit Γ (.sort false)).app _ σ.op ρ)
      ((rawInterpret piLimit Γ p).app _ σ.op ρ) = (rawInterpret piLimit Γ p).app _ σ.op ρ)
    (ihh : piLimit.rawExtend ((rawInterpret piLimit Γ p).app _ σ.op ρ)
      ((rawInterpret piLimit Γ h).app _ σ.op ρ) = (rawInterpret piLimit Γ h).app _ σ.op ρ)
    (ihh' : piLimit.rawExtend ((rawInterpret piLimit Γ p).app _ σ.op ρ)
      ((rawInterpret piLimit Γ h').app _ σ.op ρ) = (rawInterpret piLimit Γ h').app _ σ.op ρ) :
    (rawInterpret piLimit Γ h).app _ σ.op ρ = (rawInterpret piLimit Γ h').app _ σ.op ρ := by
  rw [rawInterpret, RawFamily.sort_value] at ihp
  calc
    _ = _ := ihh.symm
    _ = _ := piLimit_rawExtend_prop ihp _
    _ = _ := (piLimit_rawExtend_prop ihp _).symm
    _ = _ := ihh'

end DomainSemantics.CoherentShape
