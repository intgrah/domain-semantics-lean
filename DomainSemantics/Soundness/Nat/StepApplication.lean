/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Soundness.EliminationRules
import DomainSemantics.Soundness.Nat.Rules
import DomainSemantics.Soundness.Nat.StepTyping

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ Γ₁ : Ctx} {C n b r : Term} {v : Bool}

theorem rawInterpret_natStep_application
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hn : Γ.as.terms ⊢ n : .nat)
    (hr : Γ.as.terms ⊢ r : C.inst n)
    (pC : RawJudgment (Ctx.extension Γ IsDefEq.nat) C C (.sort v))
    (pn : RawJudgment Γ n n .nat)
    (pb : RawJudgment Γ b b (Term.natRecType C))
    (hRI : HasIdeality Γ r)
    (σ : Γ₁ ⟶ Γ) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret piLimit Γ (.app (.app b n) r)).app _ σ.op ρ =
      rawApplication
        (rawApplication ((rawInterpret piLimit Γ b).app _ σ.op ρ)
          {Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat hn)}
          ((rawInterpret piLimit Γ n).app _ σ.op ρ))
        {Tm.presheaf.map σ.op
          (Tm.pairOfTyping Γ.as.wf (IsDefEq.inst0 Γ.as.wf hn hC) hr)}
        ((rawInterpret piLimit Γ r).app _ σ.op ρ) := by
  let Γn := Ctx.extension Γ (IsDefEq.nat : Γ.as.terms ⊢ .nat : .type)
  have hstep : C :: Γn.as.terms ⊢ Term.natRecStep C : .sort v :=
    IsDefEq.natRecStep_ty Γ.as.wf hC
  have hbody : Γn.as.terms ⊢ .forallE C (Term.natRecStep C) : .sort v :=
    IsDefEq.forallEDF₀ Γn.as.wf hC hstep
  have hready : PiReady Γ .nat (.forallE C (Term.natRecStep C)) := pb.type.ready
  let F := pb.eval hρ
  let N := pn.eval hρ
  let X := hρ.eval hRI
  let predecessor := Tm.presheaf.map σ.op (Tm.pairOfTyping Γ.as.wf .nat hn)
  let result := Tm.presheaf.map σ.op
    (Tm.pairOfTyping Γ.as.wf (IsDefEq.inst0 Γ.as.wf hn hC) hr)
  let G := application F predecessor N
  let s := (Raw.ContextSection.ofTerm IsDefEq.nat hn).pullbackId σ
  have hs : SourceAdmissible s.hom (ρ.push N.val) :=
    hρ.push IsDefEq.nat s (HasIdeality.nat Γ σ ρ hρ)
      N.property (pn.eval_fixed hρ)
  have hinner : PiReady Γn C (Term.natRecStep C) := PiReady.natRecInner hC pC
  have houter : (rawInterpret piLimit Γ (.app b n)).app _ σ.op ρ = G.val :=
    hready.application_value IsDefEq.nat hbody hn pb.left.ideal pn.left.ideal pb.fixed
      σ ρ hρ
  have hGfixed := hready.application_fixed IsDefEq.nat hbody σ ρ hρ s
    (F := F) (X := N) (pb.eval_fixed hρ) (pn.eval_fixed hρ)
  have hsecond := hinner.application_value_subst hC hstep (Raw.Hom.one Γ.as.wf hn)
    hr σ (ρ.push N.val) hs hGfixed X
  change rawApplication ((rawInterpret piLimit Γ (.app b n)).app _ σ.op ρ)
    (Tm.presheaf.map σ.op '' RawFamily.sourceQuery Γ r) X.val =
    rawApplication (rawApplication F.val {predecessor} N.val) {result} X.val
  rw [houter, rawApplication_singleton F N predecessor,
    rawApplication_singleton G X result]
  exact hsecond

end DomainSemantics.CoherentShape
