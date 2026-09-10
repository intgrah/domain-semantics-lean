/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Universe

@[expose] public section

namespace DomainSemantics.CoherentShape

variable {Γ : Ctx}

theorem isCode_type_piGenerator (label : Σ A : Ty Γ, Ty (Γ.extend A)) (a : CoherentShape Γ)
    (f : CoherentGraph Γ) : IsCode true (piGenerator label a f) := .forallE

theorem isCode_prop_piGenerator (label : Σ A : Ty Γ, Ty (Γ.extend A)) (a : CoherentShape Γ)
    (f : CoherentGraph Γ) (hf : ∀ i, IsCode false (f.output i)) :
    IsCode false (piGenerator label a f) :=
  .forallE_prop hf

end DomainSemantics.CoherentShape
