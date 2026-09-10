/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Soundness.BinderRules
import DomainSemantics.Soundness.Nat.Rules
import DomainSemantics.Soundness.StructuralRules

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {Γ Γ₁ : Ctx} {C : Term} {v : Bool}

namespace NatStep

abbrev context (hC : .nat :: Γ.as.terms ⊢ C : .sort v) : Ctx :=
  Ctx.extension (Ctx.extension Γ IsDefEq.nat) hC

def baseMap (hC : .nat :: Γ.as.terms ⊢ C : .sort v) : Ctx.VariableMap (context hC) Γ :=
  (Ctx.VariableMap.projection (Γ.extension IsDefEq.nat) hC).tail IsDefEq.nat

theorem predecessor_typed (hC : .nat :: Γ.as.terms ⊢ C : .sort v) :
    (context hC).as.terms ⊢ .bvar 1 : .nat :=
  IsDefEq.bvar₀ (context hC).as.wf (Lookup.succ Lookup.zero)

def substitution (hC : .nat :: Γ.as.terms ⊢ C : .sort v) :
    ((context hC).as ⟶ (Ctx.extension Γ IsDefEq.nat).as) :=
  (baseMap hC).toRawHom.cons IsDefEq.nat (.succ (.bvar 1))
    (IsDefEq.succDF (predecessor_typed hC))

theorem subst_eq_step (hC : .nat :: Γ.as.terms ⊢ C : .sort v) :
    C.subst (substitution hC).subst = Term.natRecStep C := by
  rw [Term.natRecStep, Term.inst, subst_lift']
  congr 1
  funext i
  cases i <;> rfl

theorem predecessor_ideal (hC : .nat :: Γ.as.terms ⊢ C : .sort v) :
    HasIdeality (context hC) (.bvar 1) :=
  fun _ _ hρ => ((SourceAdmissible.cons_iff IsDefEq.nat _ _).mp (hρ.tail hC)).2.2.1

theorem predecessor_fixed (hC : .nat :: Γ.as.terms ⊢ C : .sort v) :
    HasFixedness (context hC) (.bvar 1) .nat := by
  intro Γ₁ σ ρ hρ
  have h := ((SourceAdmissible.cons_iff IsDefEq.nat _ _).mp (hρ.tail hC)).2.2.2
  change piLimit.rawExtend ((RawFamily.nat : RawFamily Γ).app _ _ _) (ρ 1) = ρ 1 at h
  change piLimit.rawExtend ((RawFamily.nat : RawFamily (context hC)).app _ σ.op ρ) (ρ 1) = ρ 1
  simpa only [RawFamily.nat_value] using h

theorem source_admissible (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (σ : Γ₁ ⟶ context hC) (ρ : RawValuation Γ₁) (hρ : SourceAdmissible σ ρ) :
    SourceAdmissible (σ ≫ RawCtx.toCtx.map (substitution hC))
      (ρ.tail.tail.push ((rawInterpret piLimit (context hC) (.succ (.bvar 1))).app _ σ.op ρ)) := by
  have hbase : SourceAdmissible (σ ≫ (baseMap hC).hom) ρ.tail.tail := by
    simpa [baseMap, ← Category.assoc] using (hρ.tail hC).tail IsDefEq.nat
  refine hbase.push IsDefEq.nat
    ((Raw.ContextSection.ofTyping IsDefEq.nat (baseMap hC).toRawHom _
      (IsDefEq.succDF (predecessor_typed hC))).pullback σ)
    (HasIdeality.nat Γ _ _ hbase)
    (HasIdeality.succ (predecessor_typed hC) (predecessor_ideal hC) σ ρ hρ) ?_
  simpa only [rawInterpret.eq_3, RawFamily.nat_value] using
    HasFixedness.succ (predecessor_typed hC) (predecessor_fixed hC) σ ρ hρ

end NatStep

theorem HasIdeality.natRecStep (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (hCI : HasIdeality (Ctx.extension Γ IsDefEq.nat) C)
    (hCS : HasSubstitution (Ctx.extension Γ IsDefEq.nat) C) :
    HasIdeality (NatStep.context hC) (Term.natRecStep C) := by
  intro Γ₁ σ ρ hρ
  have hs := NatStep.source_admissible hC σ ρ hρ
  rw [← NatStep.subst_eq_step hC, hCS (NatStep.substitution hC) σ _ ρ
    (SingleSubstitution.oneAlong IsDefEq.nat (NatStep.baseMap hC)
      (IsDefEq.succDF (NatStep.predecessor_typed hC))
      (HasRenaming.of_substitution (HasSubstitution.succ (NatStep.predecessor_typed hC)
        (HasSubstitution.bvar (NatStep.context hC) 1))) σ ρ hρ) hs]
  exact fun {_} => hCI _ _ hs

theorem PiReady.natRecInner (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (pC : RawJudgment (Ctx.extension Γ IsDefEq.nat) C C (.sort v)) :
    PiReady (Ctx.extension Γ IsDefEq.nat) C (Term.natRecStep C) :=
  PiReady.of_ideality hC (IsDefEq.natRecStep_ty Γ.as.wf hC) pC.left.ideal
    (HasIdeality.natRecStep hC pC.left.ideal pC.left.subst)

end DomainSemantics.CoherentShape
