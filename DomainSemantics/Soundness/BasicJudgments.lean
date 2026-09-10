/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Judgment
import DomainSemantics.Soundness.ComputationRules
import DomainSemantics.Soundness.StructuralRules

@[expose] public section

namespace DomainSemantics.CoherentShape

variable {Γ : Ctx} {A A' B C a a' b b' t t' p x h : Term} {u v : Bool}

namespace RawTermProperties

theorem sort (Γ : Ctx) (u : Bool) : RawTermProperties Γ (.sort u) where
  ideal := HasIdeality.sort Γ u
  subst := HasSubstitution.sort Γ u
  ready := True.intro

theorem refl (Γ : Ctx) (a : Term) : RawTermProperties Γ (.refl a) where
  ideal := HasIdeality.refl Γ a
  subst := HasSubstitution.refl Γ a
  ready := True.intro

theorem identity (pA : RawTermProperties Γ A) (pa : RawTermProperties Γ a)
    (pb : RawTermProperties Γ b) : RawTermProperties Γ (.id A a b) where
  ideal := HasIdeality.identity pA.ideal pa.ideal pb.ideal
  subst := HasSubstitution.identity pA.subst pa.subst pb.subst
  ready := True.intro

end RawTermProperties

namespace RawJudgment

theorem of_typings (pt : RawJudgment Γ t t A) (pt' : RawJudgment Γ t' t' A)
    (heq : HasEquality Γ t t') : RawJudgment Γ t t' A where
  regular := pt.regular
  type := pt.type
  left := pt.left
  right := pt'.left
  equal := heq
  fixed := pt.fixed

theorem bvar {i : ℕ} (hi : Lookup Γ.as.terms i A) (hA : Γ.as.terms ⊢ A : .sort u)
    (pA : RawJudgment Γ A A (.sort u)) (hΓ : ContextRen Γ) :
    RawJudgment Γ (.bvar i) (.bvar i) A := by
  let pvar : RawTermProperties Γ (.bvar i) := {
    ideal := fun σ ρ hρ ↦ (hΓ.bvar hi σ ρ hρ).1
    subst := HasSubstitution.bvar Γ i
    ready := True.intro
  }
  exact {
    regular := ⟨u, hA, pA.fixed⟩
    type := pA.left
    left := pvar
    right := pvar
    equal := HasEquality.refl Γ _
    fixed := fun σ ρ hρ ↦ (hΓ.bvar hi σ ρ hρ).2
  }

theorem sort (Γ : Ctx) (u : Bool) : RawJudgment Γ (.sort u) (.sort u) .type where
  regular := ⟨true, IsDefEq.sort, HasFixedness.sort Γ true⟩
  type := RawTermProperties.sort Γ true
  left := RawTermProperties.sort Γ u
  right := RawTermProperties.sort Γ u
  equal := HasEquality.refl Γ _
  fixed := HasFixedness.sort Γ u

theorem idDF (pA : RawJudgment Γ A A' (.sort u)) (pa : RawJudgment Γ a a' A)
    (pb : RawJudgment Γ b b' A) : RawJudgment Γ (.id A a b) (.id A' a' b') .prop where
  regular := ⟨true, IsDefEq.sort, HasFixedness.sort Γ false⟩
  type := RawTermProperties.sort Γ false
  left := RawTermProperties.identity pA.left pa.left pb.left
  right := RawTermProperties.identity pA.right pa.right pb.right
  equal := HasEquality.identity pA.equal pa.equal pb.equal
  fixed := HasFixedness.identity Γ A a b

theorem reflDF (hId : Γ.as.terms ⊢ .id A a a : .prop)
    (pId : RawJudgment Γ (.id A a a) (.id A a a) .prop) :
    RawJudgment Γ (.refl a) (.refl a') (.id A a a) where
  regular := ⟨false, hId, pId.fixed⟩
  type := pId.left
  left := RawTermProperties.refl Γ a
  right := RawTermProperties.refl Γ a'
  equal := HasEquality.refl_term Γ a a'
  fixed := HasFixedness.refl Γ a (.id A a a)

theorem proofIrrel (pp : RawJudgment Γ p p .prop)
    (pt : RawJudgment Γ t t p) (pt' : RawJudgment Γ t' t' p) :
    RawJudgment Γ t t' p :=
  of_typings pt pt' (HasEquality.proofIrrel pp.fixed pt.fixed pt'.fixed)

theorem beta (hA : Γ.as.terms ⊢ A : .sort u) (ha : Γ.as.terms ⊢ a : A)
    (pA : RawJudgment Γ A A (.sort u))
    (pb : RawJudgment (Ctx.extension Γ hA) b b B)
    (pa : RawJudgment Γ a a A)
    (pApp : RawJudgment Γ (.app (.lam A b) a) (.app (.lam A b) a) (B.inst a))
    (pInst : RawJudgment Γ (b.inst a) (b.inst a) (B.inst a)) :
    RawJudgment Γ (.app (.lam A b) a) (b.inst a) (B.inst a) :=
  of_typings pApp pInst
    (HasEquality.beta hA ha pA.left.ideal pb.left.ideal pa.left.ideal pa.fixed
      pa.left.ren pb.left.subst)

theorem tr_K (hA : Γ.as.terms ⊢ A : .sort u) (hab : Γ.as.terms ⊢ a ≡ b : A)
    (pA : RawJudgment Γ A A (.sort u)) (pab : RawJudgment Γ a b A)
    (pC : RawJudgment (Ctx.extension Γ hA) C C (.sort v))
    (px : RawJudgment Γ x x (C.inst a))
    (pTr : RawJudgment Γ (.tr A a b C x h) (.tr A a b C x h) (C.inst b))
    (pTarget : RawJudgment Γ x x (C.inst b)) :
    RawJudgment Γ (.tr A a b C x h) x (C.inst b) :=
  of_typings pTr pTarget
    (HasEquality.tr_K hA hab pA.left.ideal pab.left.ideal pab.fixed pab.left.ren
      pab.equal pC.left.subst px.fixed)

end RawJudgment

end DomainSemantics.CoherentShape

namespace DomainSemantics.CoherentShape

open CodeAssignment

variable {Γ : Ctx} {A a b C x h : Term} {u : Bool}

theorem RawTermProperties.transport (hA : Γ.as.terms ⊢ A : .sort u) (hb : Γ.as.terms ⊢ b : A)
    (hAI : HasIdeality Γ A) (pb : RawTermProperties Γ b) (hbF : HasFixedness Γ b A)
    (pC : RawTermProperties (Ctx.extension Γ hA) C) (px : RawTermProperties Γ x)
    (hTI : HasIdeality Γ (C.inst b)) : RawTermProperties Γ (.tr A a b C x h) where
  ideal := by
    intro Γ₁ σ ρ hρ
    rw [rawInterpret_transport_value hA hb hAI pb.ideal hbF pb.ren pC.subst σ ρ hρ]
    exact piLimit.rawExtend_isDirected (hTI σ ρ hρ) (px.ideal σ ρ hρ)
  subst := HasSubstitution.tr hA hb hAI pb.ideal hbF pb.subst pC.subst px.subst
  ready := True.intro

theorem RawJudgment.trDF {A' a' b' C' x' h' : Term} {v : Bool}
    (hAA' : Γ.as.terms ⊢ A ≡ A' : .sort u) (hbb' : Γ.as.terms ⊢ b ≡ b' : A)
    (hTarget : Γ.as.terms ⊢ C.inst b ≡ C'.inst b' : .sort v)
    (pA : RawJudgment Γ A A' (.sort u)) (pb : RawJudgment Γ b b' A)
    (pC : RawJudgment (Ctx.extension Γ hAA'.hasType.1) C C' (.sort v))
    (pC' : RawJudgment (Ctx.extension Γ hAA'.hasType.2) C C' (.sort v))
    (px : RawJudgment Γ x x' (C.inst a))
    (pTarget : RawJudgment Γ (C.inst b) (C'.inst b') (.sort v)) :
    RawJudgment Γ (.tr A a b C x h) (.tr A' a' b' C' x' h') (C.inst b) := by
  have hb' : Γ.as.terms ⊢ b' : A' := hAA'.defeqDF hbb'.hasType.2
  have hbF' : HasFixedness Γ b' A' :=
    HasFixedness.convert pb.fixed_right pA.equal
  refine {
    regular := ⟨v, hTarget.hasType.1, pTarget.fixed⟩
    type := pTarget.left
    left := RawTermProperties.transport hAA'.hasType.1 hbb'.hasType.1
      pA.left.ideal pb.left pb.fixed pC.left px.left pTarget.left.ideal
    right := RawTermProperties.transport hAA'.hasType.2 hb'
      pA.right.ideal pb.right hbF' pC'.right px.right pTarget.right.ideal
    equal := ?_
    fixed := ?_
  }
  · intro Γ₁ σ ρ hρ
    rw [rawInterpret_transport_value hAA'.hasType.1 hbb'.hasType.1
        pA.left.ideal pb.left.ideal pb.fixed pb.left.ren pC.left.subst σ ρ hρ,
      rawInterpret_transport_value hAA'.hasType.2 hb'
        pA.right.ideal pb.right.ideal hbF' pb.right.ren pC'.right.subst σ ρ hρ,
      pTarget.equal σ ρ hρ, px.equal σ ρ hρ]
  · intro Γ₁ σ ρ hρ
    rw [rawInterpret_transport_value hAA'.hasType.1 hbb'.hasType.1
      pA.left.ideal pb.left.ideal pb.fixed pb.left.ren pC.left.subst σ ρ hρ]
    exact piLimit.rawExtend_idempotent piLimit_isIdempotent (pTarget.left.ideal σ ρ hρ) (px.left.ideal σ ρ hρ)

end DomainSemantics.CoherentShape
