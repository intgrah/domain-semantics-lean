/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics.CoherentShape

variable {Γ : Ctx} {C M a b : Term} {v : Bool}

theorem rawInterpret_natRec (D : CodeAssignment)
    (hC : .nat :: Γ.as.terms ⊢ C : .sort v) (hM : Γ.as.terms ⊢ M : .nat)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C) :
    rawInterpret D Γ (.natRec C M a b) =
      RawFamily.natRec D hC hM ha hb
        (rawInterpret D (Ctx.extension Γ .nat) C)
        (rawInterpret D Γ M) (rawInterpret D Γ a) (rawInterpret D Γ b) :=
  RawFamily.iSup_eq ⟨v, hC, hM, ha, hb⟩ fun ⟨_, hC', hM', ha', hb'⟩ => by
    unfold RawFamily.natRec
    rw [NatRecLabelRelation.syntactic_congr hC' ha' hb']

end DomainSemantics.CoherentShape
