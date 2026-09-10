/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Interpretation.Nat.Witnesses
import DomainSemantics.Soundness.BasicJudgments
import DomainSemantics.Soundness.BinderRules
import DomainSemantics.Soundness.Nat.RecStructural
import DomainSemantics.Soundness.Nat.Rules

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ : Ctx} {C C' M M' a a' b b' : Term} {v : Bool}

theorem rawInterpret_natRec_value (D : CodeAssignment)
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) :
    (rawInterpret D Γ (.natRec C M a b)).app _ σ.op ρ =
      (RawAction.natRec D
        (RawFamily.normalizedBodyAction D (Ctx.rawDisplay .nat) (rawInterpret D Γ .nat)
          (rawInterpret D (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C) σ ρ)
        ((NatRecLabelRelation.syntactic hC ha hb).pullback σ)
        ((rawInterpret D Γ a).app _ σ.op ρ) ((rawInterpret D Γ b).app _ σ.op ρ)).app _ ((𝟙 Γ₁).op, Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat hM))
          ((rawInterpret D Γ M).app _ σ.op ρ) := by
  rw [rawInterpret_natRec D hC hM ha hb]
  rfl

theorem rawInterpret_natMotive_value (hM : Γ.as.terms ⊢ M : .nat)
    (hMI : HasIdeality Γ M) (hMF : HasFixedness Γ M .nat)
    (hMR : HasRenaming Γ M)
    (hCS : HasSubstitution (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay .nat) (rawInterpret piLimit Γ .nat)
      (rawInterpret piLimit (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
      σ ρ).app _ (𝟙 (Opposite.op Γ₁), Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat hM))
        ((rawInterpret piLimit Γ M).app _ σ.op ρ) =
      (rawInterpret piLimit Γ (C[M/])).app _ σ.op ρ := by
  change RawFamily.normalizedSectionValue piLimit (Ctx.rawDisplay .nat)
    (rawInterpret piLimit Γ .nat) (rawInterpret piLimit (Γ.extension .nat) C)
    (𝟙 Γ₁ ≫ σ) (ρ.pullback (𝟙 Γ₁)) _ _ = _
  simp [RawFamily.normalizedSectionValue]
  erw [hMF σ ρ hρ, RawFamily.sectionValue_eq_value (Ctx.rawDisplay .nat) _ σ ρ _ _
    ((Raw.ContextSection.ofTerm .nat hM).pullbackId σ)]
  exact HasSubstitution.instantiate .nat hM (HasIdeality.nat Γ) hMI hMF hMR hCS σ ρ hρ

theorem HasIdeality.natRec (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (hCI : HasIdeality (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (hMI : HasIdeality Γ M) (haI : HasIdeality Γ a) (hbI : HasIdeality Γ b) :
    HasIdeality Γ (.natRec C M a b) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_natRec_value piLimit hC hM ha hb]
  exact RawAction.IsIdealValued.natRec piLimit
    (HasIdeality.bodyAction .nat (HasIdeality.nat Γ) hCI σ ρ hρ) _
    (haI σ ρ hρ) (hbI σ ρ hρ) (𝟙 Γ₁) _
    (hρ.eval hMI)

theorem HasFixedness.natRec (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (hCI : HasIdeality (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (hMI : HasIdeality Γ M) (hMF : HasFixedness Γ M .nat) (hMR : HasRenaming Γ M)
    (hCS : HasSubstitution (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (haI : HasIdeality Γ a) (hbI : HasIdeality Γ b) :
    HasFixedness Γ (.natRec C M a b) (C[M/]) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_natRec_value piLimit hC hM ha hb,
    ← rawInterpret_natMotive_value hM hMI hMF hMR hCS σ ρ hρ]
  exact RawAction.natRec_fixed piLimit piLimit_isIdempotent _
    (HasIdeality.bodyAction .nat (HasIdeality.nat Γ) hCI σ ρ hρ) _ _ _
    (haI σ ρ hρ) (hbI σ ρ hρ) (𝟙 Γ₁) _
    (hρ.eval hMI)

theorem HasEquality.natRec (hCC' : .nat :: Γ.as.terms ⊢ C ≡ C' : .sort v)
    (hMM' : Γ.as.terms ⊢ M ≡ M' : .nat)
    (haa' : Γ.as.terms ⊢ a ≡ a' : C[Term.zero/])
    (hbb' : Γ.as.terms ⊢ b ≡ b' : Term.natRecType C)
    (hCE : HasEquality (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C C')
    (hCR : HasRenaming (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C')
    (hMI : HasIdeality Γ M) (hME : HasEquality Γ M M')
    (haE : HasEquality Γ a a') (hbE : HasEquality Γ b b') :
    HasEquality Γ (.natRec C M a b) (.natRec C' M' a' b') := by
  have ha' := (IsDefEq.instDF Γ.as.wf .nat hCC' .zero).defeqDF haa'.hasType.2
  have hb' := (IsDefEq.natRecTypeDF Γ.as.wf hCC').defeqDF hbb'.hasType.2
  have hR := NatRecLabelRelation.syntactic_congr
    (hC := hCC'.hasType.1) (hC' := hCC'.hasType.2)
    (ha := haa'.hasType.1) (ha' := ha')
    (hb := hbb'.hasType.1) (hb' := hb') hCC' haa' hbb'
  have hlabel := Tm.pairOfTyping_congr Γ.as.wf (.nat : Γ.as.terms ⊢ .nat : .type) hMM'
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_natRec_value piLimit hCC'.hasType.1 hMM'.hasType.1
      haa'.hasType.1 hbb'.hasType.1,
    rawInterpret_natRec_value piLimit hCC'.hasType.2 hMM'.hasType.2 ha' hb',
    ← hR, ← hlabel, ← hME σ ρ hρ, ← haE σ ρ hρ, ← hbE σ ρ hρ]
  apply RawAction.natRec_eq_on_ideals piLimit
    (I := hρ.eval hMI)
  exact normalizedBodyAction_contextConversion (.nat : Γ.as.terms ⊢ .nat : .type)
    (HasIdeality.nat Γ) (HasEquality.refl Γ .nat) hCE hCR σ ρ hρ

theorem HasEquality.natRec_zero (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (hCS : HasSubstitution (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (haF : HasFixedness Γ a (C[Term.zero/])) :
    HasEquality Γ (.natRec C .zero a b) a := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_natRec_value piLimit hC .zero ha hb]
  change (RawAction.natRec piLimit _ _ _ _).app _ ((𝟙 Γ₁).op, _)
    ((RawFamily.zero : RawFamily Γ).app _ σ.op ρ) = _
  simp
  change (RawAction.natRec piLimit _ _ _ _).app _ ((𝟙 Γ₁).op, _)
    (ΩLower.principal pointedOrder zeroAtom) = _
  rw [RawAction.natRec_zero, op_id, ΩLower.pullback_id]
  have hcode := rawInterpret_natMotive_value (.zero : Γ.as.terms ⊢ .zero : .nat)
    (HasIdeality.zero Γ) (HasFixedness.zero Γ) (HasRenaming.of_substitution (HasSubstitution.zero Γ)) hCS σ ρ hρ
  simp [rawInterpret] at hcode
  change (RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay .nat) (rawInterpret piLimit Γ .nat)
    (rawInterpret piLimit (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C) σ ρ).app _ (𝟙 (Opposite.op Γ₁), Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat .zero))
      (ΩLower.principal pointedOrder zeroAtom) = _ at hcode
  rw [hcode]
  exact haF σ ρ hρ

theorem RawTermProperties.natRec (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (pC : RawTermProperties (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (pM : RawTermProperties Γ M) (pa : RawTermProperties Γ a)
    (pb : RawTermProperties Γ b) : RawTermProperties Γ (.natRec C M a b) where
  ideal := HasIdeality.natRec hC hM ha hb pC.ideal pM.ideal pa.ideal pb.ideal
  subst := HasSubstitution.natRec hC hM ha hb pM.ideal pC.subst pM.subst pa.subst pb.subst
  ready := True.intro

theorem RawJudgment.natRecDF (hCC' : .nat :: Γ.as.terms ⊢ C ≡ C' : .sort v)
    (hMM' : Γ.as.terms ⊢ M ≡ M' : .nat)
    (haa' : Γ.as.terms ⊢ a ≡ a' : C[Term.zero/])
    (hbb' : Γ.as.terms ⊢ b ≡ b' : Term.natRecType C)
    (hResult : Γ.as.terms ⊢ C[M/] ≡ C'[M'/] : .sort v)
    (pC : RawJudgment (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C C' (.sort v))
    (pM : RawJudgment Γ M M' .nat) (pa : RawJudgment Γ a a' (C[Term.zero/]))
    (pb : RawJudgment Γ b b' (Term.natRecType C))
    (pResult : RawJudgment Γ (C[M/]) (C'[M'/]) (.sort v)) :
    RawJudgment Γ (.natRec C M a b) (.natRec C' M' a' b') (C[M/]) where
  regular := ⟨v, hResult.hasType.1, pResult.fixed⟩
  type := pResult.left
  left := RawTermProperties.natRec hCC'.hasType.1 hMM'.hasType.1
    haa'.hasType.1 hbb'.hasType.1 pC.left pM.left pa.left pb.left
  right := RawTermProperties.natRec hCC'.hasType.2 hMM'.hasType.2
    ((IsDefEq.instDF Γ.as.wf .nat hCC' .zero).defeqDF haa'.hasType.2)
    ((IsDefEq.natRecTypeDF Γ.as.wf hCC').defeqDF hbb'.hasType.2)
    pC.right pM.right pa.right pb.right
  equal := HasEquality.natRec hCC' hMM' haa' hbb' pC.equal pC.right.ren pM.left.ideal pM.equal pa.equal pb.equal
  fixed := HasFixedness.natRec hCC'.hasType.1 hMM'.hasType.1
    haa'.hasType.1 hbb'.hasType.1 pC.left.ideal pM.left.ideal pM.fixed pM.left.ren pC.left.subst pa.left.ideal pb.left.ideal

theorem RawJudgment.natRec_zero (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (pC : RawJudgment (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C C (.sort v))
    (pa : RawJudgment Γ a a (C[Term.zero/]))
    (pRec : RawJudgment Γ (.natRec C .zero a b) (.natRec C .zero a b) (C[Term.zero/])) :
    RawJudgment Γ (.natRec C .zero a b) a (C[Term.zero/]) :=
  of_typings pRec pa (HasEquality.natRec_zero hC ha hb pC.left.subst pa.fixed)

end DomainSemantics.CoherentShape
