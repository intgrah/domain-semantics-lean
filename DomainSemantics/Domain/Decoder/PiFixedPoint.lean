/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiStages
public import DomainSemantics.Domain.Pi
import DomainSemantics.Domain.Decoder.PiDecoderEquation

@[expose] public section

namespace DomainSemantics.CoherentShape.CodeAssignment

open CategoryTheory

variable {Γ Γ₁ : Ctx}

theorem piLimit_fixedPoint : piLimit.piStep = piLimit := by
  refine NatTrans.ext (funext fun Γ₁ => Preord.ext fun ⟨a, ha⟩ => ?_)
  exact piStepValue_eq_of_rank
    (fun b hb => by rw [piLimit_app, piStage_value_stable _ b le_rfl (Nat.lt_succ_self _) hb])
    a ha le_rfl

theorem piLimit_decode_sort (r : Bool) :
    piLimit.decode (principalIdeal (sortAtom r : CoherentShape Γ)) = universeOperator r := by
  rw [decode_principal, ← piLimit_fixedPoint]
  rfl

theorem piLimit_decode_pi (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (A : Domain Γ) (B : IdealAction Γ) :
    piLimit.decode (pi label A B) = piLimit.piOperator A B :=
  calc
    piLimit.decode (pi label A B) = piLimit.piStep.decode (pi label A B) :=
      congrArg (fun D : CodeAssignment ↦ D.decode (pi label A B)) piLimit_fixedPoint.symm
    _ = _ := decode_piStep_pi piLimit label A B

theorem piLimit_extend_pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : Domain Γ) (B : IdealAction Γ)
    (G : Domain Γ) :
    piLimit.extend (pi label A B) G = (piLimit.piOperator A B).val.app _ (𝟙 Γ).op G := by
  simpa [decode] using congrArg (fun P : IdealOperator Γ ↦ P.val.app _ (𝟙 Γ).op G)
    (piLimit_decode_pi label A B)

theorem piLimit_extend_sort (r : Bool) (X : Domain Γ) :
    piLimit.extend (principalIdeal (sortAtom r)) X = universeIdeal r X := by
  have h := congrArg (fun P : IdealOperator Γ ↦ P.val.app _ (𝟙 Γ).op X) (piLimit_decode_sort r)
  change piLimit.extend ((principalIdeal (sortAtom r)).pullback (𝟙 Γ)) X = universeIdeal r X at h
  simpa using h

end DomainSemantics.CoherentShape.CodeAssignment
