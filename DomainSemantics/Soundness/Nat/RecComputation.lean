/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Soundness.BasicJudgments
import DomainSemantics.Soundness.Nat.RecRules
import DomainSemantics.Soundness.Nat.Rules
import DomainSemantics.Soundness.Nat.StepApplication

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ Γ₁ : Ctx} {C n a b : Term} {v : Bool}

theorem rawInterpret_natRec_succ_projected
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hn : Γ.as.terms ⊢ n : .nat)
    (ha : Γ.as.terms ⊢ a : C.inst .zero) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (hCI : HasIdeality (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (hnI : HasIdeality Γ n) (hnF : HasFixedness Γ n .nat) (hnS : HasSubstitution Γ n)
    (hCS : HasSubstitution (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C)
    (haI : HasIdeality Γ a) (hbI : HasIdeality Γ b)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret piLimit Γ (.natRec C (.succ n) a b)).app _ σ.op ρ =
      piLimit.rawExtend ((rawInterpret piLimit Γ (C.inst (.succ n))).app _ σ.op ρ)
        (rawApplication
          (rawApplication ((rawInterpret piLimit Γ b).app _ σ.op ρ)
            {Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat hn)}
            ((rawInterpret piLimit Γ n).app _ σ.op ρ))
          {Tm.presheaf.map σ.op
            (Tm.pairOfTyping Γ.as.wf (IsDefEq.inst0 Γ.as.wf hn hC)
              (IsDefEq.natRecDF₀ Γ.as.wf hC hn ha hb))}
          ((rawInterpret piLimit Γ (.natRec C n a b)).app _ σ.op ρ)) := by
  let U := RawFamily.normalizedBodyAction piLimit (Ctx.rawDisplay .nat) (rawInterpret piLimit Γ .nat)
    (rawInterpret piLimit (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C) σ ρ
  let R := (NatRecLabelRelation.syntactic hC ha hb).pullback σ
  let N := hρ.eval hnI
  let Z := hρ.eval haI
  let B := hρ.eval hbI
  let predecessor := Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat hn)
  let result := Tm.presheaf.map σ.op
    (Tm.pairOfTyping Γ.as.wf (IsDefEq.inst0 Γ.as.wf hn hC)
      (IsDefEq.natRecDF₀ Γ.as.wf hC hn ha hb))
  let successor := Tm.presheaf.map σ.op
    (Tm.pairOfTyping Γ.as.wf .nat (IsDefEq.succDF hn))
  have hU : U.IsFinitary := RawFamily.normalizedBodyAction_isFinitary piLimit (Ctx.rawDisplay .nat) _
    (rawInterpret_isFinitary piLimit _ C) σ ρ
  have hUI : U.IsIdealValued :=
    HasIdeality.bodyAction .nat (HasIdeality.nat Γ) hCI σ ρ hρ
  have hR : R.holds (𝟙 Γ₁) predecessor result := by
    have h : (NatRecLabelRelation.syntactic hC ha hb).holds (𝟙 Γ)
        (Tm.pairOfTyping Γ.as.wf .nat hn)
        (Tm.pairOfTyping Γ.as.wf (IsDefEq.inst0 Γ.as.wf hn hC)
          (IsDefEq.natRecDF₀ Γ.as.wf hC hn ha hb)) :=
      ⟨Raw.ContextSection.ofTerm .nat hn, Tm.natRec.app_ofTerm hC ha hb hn⟩
    simpa [R, predecessor, result] using (NatRecLabelRelation.syntactic hC ha hb).natural h σ

  have hcode : U.app _ ((𝟙 Γ₁).op, successor) (succIdeal predecessor N).val =
      (rawInterpret piLimit Γ (C.inst (.succ n))).app _ σ.op ρ := by
    have h := rawInterpret_natMotive_value (C := C) (IsDefEq.succDF hn)
      (HasIdeality.succ hn hnI) (HasFixedness.succ hn hnF)
      (HasRenaming.of_substitution (HasSubstitution.succ hn hnS)) hCS σ ρ hρ
    rw [rawInterpret_succ piLimit hn] at h
    exact h
  rw [rawInterpret_natRec_value piLimit hC (IsDefEq.succDF hn) ha hb,
    rawInterpret_succ piLimit hn]
  change (RawAction.natRec piLimit U R Z.val B.val).app _ ((𝟙 Γ₁).op, successor) (succIdeal predecessor N).val = _
  rw [RawAction.natRec_succ piLimit U hU hUI R Z B
    (𝟙 Γ₁) successor predecessor result hR N, hcode]
  congr 1
  rw [rawInterpret_natRec_value piLimit hC hn ha hb]
  simp [rawNatStep]
  rfl

theorem HasEquality.natRec_succ
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hn : Γ.as.terms ⊢ n : .nat)
    (ha : Γ.as.terms ⊢ a : C.inst .zero) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (pC : RawJudgment (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C C (.sort v))
    (pn : RawJudgment Γ n n .nat) (pa : RawJudgment Γ a a (C.inst .zero))
    (pb : RawJudgment Γ b b (Term.natRecType C))
    (hStep : HasFixedness Γ (.app (.app b n) (.natRec C n a b)) (C.inst (.succ n))) :
    HasEquality Γ (.natRec C (.succ n) a b) (.app (.app b n) (.natRec C n a b)) := by
  intro Γ₁ σ ρ hρ
  rw [rawInterpret_natRec_succ_projected hC hn ha hb pC.left.ideal
    pn.left.ideal pn.fixed pn.left.subst pC.left.subst pa.left.ideal pb.left.ideal σ ρ hρ]
  rw [← rawInterpret_natStep_application hC hn (IsDefEq.natRecDF₀ Γ.as.wf hC hn ha hb)
    pC pn pb
    (HasIdeality.natRec hC hn ha hb pC.left.ideal pn.left.ideal pa.left.ideal pb.left.ideal)
    σ ρ hρ]
  exact hStep σ ρ hρ

theorem RawJudgment.natRec_succ
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hn : Γ.as.terms ⊢ n : .nat)
    (ha : Γ.as.terms ⊢ a : C.inst .zero) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (pC : RawJudgment (Ctx.extension Γ (.nat : Γ.as.terms ⊢ .nat : .type)) C C (.sort v))
    (pn : RawJudgment Γ n n .nat) (pa : RawJudgment Γ a a (C.inst .zero))
    (pb : RawJudgment Γ b b (Term.natRecType C))
    (pRec : RawJudgment Γ (.natRec C (.succ n) a b) (.natRec C (.succ n) a b)
      (C.inst (.succ n)))
    (pStep : RawJudgment Γ (.app (.app b n) (.natRec C n a b))
      (.app (.app b n) (.natRec C n a b)) (C.inst (.succ n))) :
    RawJudgment Γ (.natRec C (.succ n) a b) (.app (.app b n) (.natRec C n a b))
      (C.inst (.succ n)) :=
  of_typings pRec pStep (HasEquality.natRec_succ hC hn ha hb pC pn pa pb pStep.fixed)

end DomainSemantics.CoherentShape
