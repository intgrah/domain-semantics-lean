/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
import DomainSemantics.Domain.Decoder.PiFixedPoint

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory

namespace CodeAssignment

variable {Γ : Ctx}

theorem piLimit_value_nat :
    piLimit.app _ (natAtom : CoherentShape Γ) = natOperator := by
  rw [← piLimit_fixedPoint]
  rfl

theorem piLimit_extend_nat (X : Domain Γ) :
    piLimit.extend (principalIdeal natAtom) X = natIdeal X := by
  rw [extend_principal]
  change (piLimit.app _ natAtom).val.app _ (𝟙 Γ).op X = natIdeal X
  rw [piLimit_value_nat]
  rfl

end CodeAssignment

end DomainSemantics.CoherentShape
