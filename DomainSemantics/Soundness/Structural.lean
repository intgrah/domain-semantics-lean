/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Admissible

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory CodeAssignment

variable {Γ Γ₁ Γ₂ : Ctx} {A b : Term} {u : Bool}

def HasIdeality (Γ : Ctx) (t : Term) : Prop :=
  ∀ {Γ₂ : Ctx} (σ : Γ₂ ⟶ Γ) (ρ : RawValuation Γ₂),
    SourceAdmissible σ ρ → ((rawInterpret piLimit Γ t).app _ σ.op ρ).IsDirected

noncomputable def SourceAdmissible.eval {σ : Γ₁ ⟶ Γ} {ρ : RawValuation Γ₁}
    (hρ : SourceAdmissible σ ρ) (ht : HasIdeality Γ b) : Domain Γ₁ :=
  ((rawInterpret piLimit Γ b).app _ σ.op ρ).toIdeal (ht σ ρ hρ)

end DomainSemantics.CoherentShape
