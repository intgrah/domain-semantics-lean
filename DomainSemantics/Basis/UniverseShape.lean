/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Join
import DomainSemantics.Meta.Judgement

@[expose] public section

namespace DomainSemantics.Shape

variable {Γ : Ctx}
variable {r : Bool}

judgement IsCode : Bool → Shape Γ → Prop where

  Basis.IsBottom a
  ──────────────────── bottom {r : Bool} {a : Shape Γ}
  IsCode r a

  ──────────────────── sort {s : Bool}
  IsCode true (.sort s)

  ──────────────────── forallE {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a : Shape Γ} {k : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A}
    {ins outs : Fin k → Shape Γ}
  IsCode true (.forallE label a k names ins outs)

  ∀ i, IsCode false (outs i)
  ──────────────────── forallE_prop {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a : Shape Γ} {k : Nat} {names : Fin k → Σ A : Ty Γ, Tm Γ A}
    {ins outs : Fin k → Shape Γ}
  IsCode false (.forallE label a k names ins outs)

  ──────────────────── nat
  IsCode true .nat

  ──────────────────── id {r : Bool} {A a b : Shape Γ}
  IsCode r (.id A a b)

namespace IsCode

theorem bot  : IsCode r (Shape.bot : Shape Γ) := .bottom .bot

theorem pi {label : Σ A : Ty Γ, Ty (Γ.extend A)} {a : Shape Γ} {f : Graph Γ} : IsCode true (Shape.pi label a f) :=
  .forallE

theorem eq_true_of_sort {s : Bool} (h : IsCode r (Shape.sort s : Shape Γ)) : r = true := by
  cases h with
  | bottom h => nomatch h
  | sort => rfl

theorem of_le {r : Bool} {a b : Shape Γ} (hab : a ≤ b) : IsCode r b → IsCode r a
  | .bottom h => .bottom (Basis.le_bot_iff.mp (hab.trans h.le))
  | .sort => match hab with
    | .collapse h => .bottom h
    | .sort _ => .sort
  | .forallE => match hab with
    | .collapse h => .bottom h
    | .forallE _ _ => .forallE
  | .forallE_prop h => match hab with
    | .collapse h => .bottom h
    | .forallE _ hf => .forallE_prop fun i => match hf i with
      | .bottom h => .bottom h
      | .mem j _ _ hout => of_le hout (h j)
  | .nat => match hab with
    | .collapse h => .bottom h
    | .nat => .nat
  | .id => match hab with
    | .collapse h => .bottom h
    | .id _ _ _ => .id

variable (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) in
theorem map {r : Bool} {a : Shape Γ} : IsCode r a → IsCode r (a.map arg pi)
  | .bottom h => .bottom (h.map arg pi)
  | .sort => .sort
  | .forallE => .forallE
  | .forallE_prop h => .forallE_prop fun i => map (h i)
  | .nat => .nat
  | .id => .id

theorem cSup {a b : Shape Γ} (ha : IsCode r a) (hb : IsCode r b) : IsCode r (a.cSup b) := by
  fun_induction Shape.cSup a b
  · exact hb
  · exact ha
  · cases ha with | bottom ha =>
      cases hb with | bottom hb =>
        exact .bottom (.lam (Graph.IsBottom.append (Basis.IsBottom.abs_iff.mp ha)
          (Basis.IsBottom.abs_iff.mp hb)))
  · exact hb
  · exact ha
  · cases ha with
    | bottom h => nomatch h
    | forallE => exact .forallE
    | forallE_prop ha =>
      cases hb with
      | bottom h => nomatch h
      | forallE_prop hb => exact .forallE_prop (Fin.addCases (by simpa [Graph.append] using ha) (by simpa [Graph.append] using hb))
  · cases ha with | bottom h => nomatch h
  · exact .id
  · exact ha

end IsCode

end DomainSemantics.Shape
