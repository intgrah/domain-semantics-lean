/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Coherent

@[expose] public section

namespace DomainSemantics.Shape

variable {Γ Γ₁ : Ctx}

def natProjection : Shape Γ → Shape Γ
  | .zero => .zero
  | .succ label a => .succ label a.natProjection
  | _ => .bot

theorem natProjection_le : ∀ a : Shape Γ, a.natProjection ≤ a := by
  intro a
  induction a with
  | zero => exact .zero
  | succ _ _ ih => exact .succ ih
  | _ => exact Basis.LE.bot _

theorem natProjection_mono {a b : Shape Γ} (h : a ≤ b) :
    a.natProjection ≤ b.natProjection := by
  cases h with
  | collapse h => cases h <;> exact .bot _
  | succ h => exact .succ (natProjection_mono h)
  | zero => exact .zero
  | _ => exact .bot _

@[simp]
theorem natProjection_idempotent : ∀ a : Shape Γ, a.natProjection.natProjection = a.natProjection := by
  intro a
  induction a <;> simp! [*]

theorem natProjection_map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) :
    ∀ a : Shape Γ, (a.map arg pi).natProjection = a.natProjection.map arg pi := by
  intro a
  induction a <;> simp! [*]

theorem IsCoherent.natProjection {Γ : Ctx} {a : Shape Γ} (ha : IsCoherent Γ a) :
    IsCoherent Γ a.natProjection := by
  induction ha with
  | zero => exact .zero
  | succ _ ih => exact .succ ih
  | _ => exact .bot

end DomainSemantics.Shape
