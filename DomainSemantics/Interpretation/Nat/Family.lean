/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.ActionFamily
public import DomainSemantics.Interpretation.Nat.Iteration
public import DomainSemantics.Interpretation.Nat.Constructors

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

namespace RawActionFamily

noncomputable def natRec (D : CodeAssignment) (C : RawActionFamily Γ) (R : NatRecLabelRelation Γ)
    (Z B : RawFamily Γ) : RawActionFamily Γ where
  app _ σ₁ := Preord.ofHom {
    toFun ρ := RawAction.natRec D (C.app _ σ₁ ρ) (R.pullback σ₁.unop)
      (Z.app _ σ₁ ρ) (B.app _ σ₁ ρ)
    monotone' _ _ h := RawAction.natRec_mono_parameters D _
      ((C.app _ σ₁).hom.monotone h) ((Z.app _ σ₁).hom.monotone h)
      ((B.app _ σ₁).hom.monotone h) }
  naturality σ₂ σ₁ := Preord.ext fun ρ =>
    (congr(RawAction.natRec D $(C.naturality_apply σ₂ σ₁ ρ)
      $((NatRecLabelRelation.pullback_comp R σ₁.unop σ₂.unop).symm)
      $(Z.naturality_apply σ₂ σ₁ ρ) $(B.naturality_apply σ₂ σ₁ ρ))).trans
      (RawAction.pullback_natRec D _ _ _ _ σ₂.unop).symm

theorem IsFinitary.natRec (D : CodeAssignment) {C : RawActionFamily Γ}
    (hC : C.IsFinitary) (R : NatRecLabelRelation Γ) {Z B : RawFamily Γ}
    (hZ : Z.IsFinitary) (hB : B.IsFinitary) : (natRec D C R Z B).IsFinitary := by
  intro Γ₁ σ i ρ X label
  exact ΩLower.IsFinitary.of_eventually fun I _ hy =>
    RawAction.natRec_eventually D (fun label X => hC.eventually σ i ρ I X label)
      (hZ.eventually σ i ρ I) (hB.eventually σ i ρ I) label X hy

end RawActionFamily

noncomputable def RawFamily.natRec (D : CodeAssignment) {C M a b : Term} {v : Bool}
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C.inst .zero) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (Csem : RawFamily (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)))
    (Msem Z B : RawFamily Γ) : RawFamily Γ :=
  (RawActionFamily.natRec D (RawActionFamily.normalizedBody D (Ctx.rawDisplay .nat) nat Csem)
    (NatRecLabelRelation.syntactic hC ha hb) Z B).apply Msem
    (Tm.pairOfTyping Γ.as.wf .nat hM)

theorem RawFamily.IsFinitary.natRec (D : CodeAssignment) {C M a b : Term} {v : Bool}
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C.inst .zero) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    {Csem : RawFamily (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type))}
    (hCs : Csem.IsFinitary) {Msem Z B : RawFamily Γ}
    (hMs : Msem.IsFinitary) (hZ : Z.IsFinitary) (hB : B.IsFinitary) :
    (natRec D hC hM ha hb Csem Msem Z B).IsFinitary := by
  apply RawActionFamily.IsFinitary.apply
    (RawActionFamily.IsFinitary.natRec D
      (RawActionFamily.IsFinitary.normalizedBody D (Ctx.rawDisplay .nat) nat_isFinitary hCs) _ hZ hB)
    _ hMs
  exact fun σ ρ => RawAction.IsFinitary.natRec D
    (normalizedBodyAction_isFinitary D (Ctx.rawDisplay .nat) nat hCs σ ρ) _ _ _

end DomainSemantics.CoherentShape
