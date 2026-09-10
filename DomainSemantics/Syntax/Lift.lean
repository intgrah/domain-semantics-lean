/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

@[expose] public section

namespace DomainSemantics

inductive Lift where
  | refl : Lift
  | skip : Lift → Lift
  | cons : Lift → Lift

namespace Lift

variable {l l₁ l₂ : Lift} {n : Nat}

@[simp] def consN (l : Lift) : Nat → Lift
  | 0 => l
  | k + 1 => .cons (consN l k)

@[simp] def comp : Lift → Lift → Lift
  | l₁, .refl => l₁
  | l₁, .skip l₂ => .skip (l₁.comp l₂)
  | .refl, .cons l₂ => .cons l₂
  | .skip l₁, .cons l₂ => .skip (l₁.comp l₂)
  | .cons l₁, .cons l₂ => .cons (l₁.comp l₂)

@[simp] theorem refl_comp : comp refl l = l := by induction l <;> simp [*]

@[simp] def depth : Lift → Nat
  | .refl => 0
  | .skip l => l.depth + 1
  | .cons l => l.depth

@[simp] protected def liftVar : Lift → Nat → Nat
  | .refl, n => n
  | .skip l, n => l.liftVar n + 1
  | .cons _, 0 => 0
  | .cons l, n + 1 => l.liftVar n + 1

theorem liftVar_comp : (comp l₁ l₂).liftVar n = l₂.liftVar (l₁.liftVar n) := by
  fun_induction comp l₁ l₂ generalizing n <;> simp_all! -failIfUnchanged
  cases n <;> simp_all!

theorem liftVar_depth_zero (h : depth l = 0) : l.liftVar n = n := by
  fun_induction Lift.liftVar l n <;> simp_all!

end Lift

end DomainSemantics
