/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Pi
public import DomainSemantics.Interpretation.Constructors
public import DomainSemantics.Interpretation.FamilyApplication
public import DomainSemantics.Interpretation.Nat.Constructors
public import DomainSemantics.Interpretation.Nat.Family
public import DomainSemantics.Interpretation.Abstraction
public import DomainSemantics.Interpretation.DecodedFamily
public import DomainSemantics.Interpretation.Substitution

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

variable (D : CodeAssignment) in
noncomputable def rawInterpret (Γ : Ctx) : Term → RawFamily Γ
  | .bvar i => RawFamily.lookup i
  | .sort u => RawFamily.sort u
  | .nat => RawFamily.nat
  | .zero => RawFamily.zero
  | .succ n =>
      ⨆ hn : Γ.as.terms ⊢ n : .nat,
        RawFamily.succ (Tm.pairOfTyping Γ.as.wf .nat hn) (rawInterpret Γ n)
  | .natRec C M a b =>
      ⨆ h : {v : Bool // .nat :: Γ.as.terms ⊢ C : .sort v ∧ Γ.as.terms ⊢ M : .nat ∧
          Γ.as.terms ⊢ a : C[Term.zero/] ∧ Γ.as.terms ⊢ b : Term.natRecType C},
        have ⟨_, hC, hM, ha, hb⟩ := h
        RawFamily.natRec D hC hM ha hb (rawInterpret (Γ.extension .nat) C)
          (rawInterpret Γ M) (rawInterpret Γ a) (rawInterpret Γ b)
  | .app f a =>
      RawFamily.application (rawInterpret Γ f) (rawInterpret Γ a) (RawFamily.sourceQuery Γ a)
  | .lam A b =>
      ⨆ h : {u : Bool // Γ.as.terms ⊢ A : .sort u},
        have ⟨_, hA⟩ := h
        RawFamily.abstraction D (Ctx.rawDisplay hA) (rawInterpret Γ A) (rawInterpret (Γ.extension hA) b)
  | .forallE A B =>
      ⨆ h : {p : Bool × Bool // Γ.as.terms ⊢ A : .sort p.1 ∧ A :: Γ.as.terms ⊢ B : .sort p.2},
        have ⟨_, hA, hB⟩ := h
        RawFamily.pi D (Ctx.rawDisplay hA) (Ty.pairOfTyping Γ.as.wf hA hB)
          (rawInterpret Γ A) (rawInterpret (Γ.extension hA) B)
  | .id A a b =>
      RawFamily.identity (rawInterpret Γ A) (rawInterpret Γ a) (rawInterpret Γ b)
  | .refl _ => ⊥
  | .tr A _ b C x _ =>
      ⨆ h : {u : Bool // Γ.as.terms ⊢ A : .sort u ∧ Γ.as.terms ⊢ b : A},
        have ⟨_, hA, hb⟩ := h
        RawFamily.decode D
          (RawFamily.instantiate (rawInterpret (Γ.extension hA) C)
            (Raw.ContextSection.ofTerm hA hb).hom (rawInterpret Γ b))
          (rawInterpret Γ x)

variable (D : CodeAssignment) in
theorem rawInterpret_isFinitary (Γ : Ctx) : ∀ t : Term, (rawInterpret D Γ t).IsFinitary
  | .bvar i => RawFamily.lookup_isFinitary i
  | .sort u => RawFamily.sort_isFinitary u
  | .app f a =>
    RawFamily.IsFinitary.application (rawInterpret_isFinitary Γ f) (rawInterpret_isFinitary Γ a) _
  | .lam A b => RawFamily.IsFinitary.iSup fun ⟨_, hA⟩ =>
    RawFamily.IsFinitary.abstraction D (Ctx.rawDisplay hA) (rawInterpret_isFinitary Γ A) (rawInterpret_isFinitary _ b)
  | .forallE A B => RawFamily.IsFinitary.iSup fun ⟨_, hA, _⟩ =>
    RawFamily.IsFinitary.pi D (Ctx.rawDisplay hA) _ (rawInterpret_isFinitary Γ A) (rawInterpret_isFinitary _ B)
  | .nat => RawFamily.nat_isFinitary
  | .zero => RawFamily.zero_isFinitary
  | .succ n => RawFamily.IsFinitary.iSup fun _ =>
    RawFamily.IsFinitary.succ (rawInterpret_isFinitary Γ n) _
  | .natRec C M a b => RawFamily.IsFinitary.iSup fun ⟨_, hC, hM, ha, hb⟩ =>
    RawFamily.IsFinitary.natRec D hC hM ha hb (rawInterpret_isFinitary _ C)
      (rawInterpret_isFinitary Γ M) (rawInterpret_isFinitary Γ a) (rawInterpret_isFinitary Γ b)
  | .id A a b => RawFamily.IsFinitary.identity (rawInterpret_isFinitary Γ A)
    (rawInterpret_isFinitary Γ a) (rawInterpret_isFinitary Γ b)
  | .refl _ => RawFamily.bottom_isFinitary
  | .tr _ _ b C x _ => RawFamily.IsFinitary.iSup fun ⟨_, hA, hb⟩ => RawFamily.IsFinitary.decode D
    (RawFamily.IsFinitary.instantiate (rawInterpret_isFinitary _ C)
      (Raw.ContextSection.ofTerm hA hb).hom (rawInterpret_isFinitary Γ b))
    (rawInterpret_isFinitary Γ x)

end DomainSemantics.CoherentShape
