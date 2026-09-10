/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Intrinsic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace DomainSemantics

inductive Shape (Γ : Ctx) : Type where
  | bot
  | sort (rel : Bool)
  | forallE (label : Σ A : Ty Γ, Ty (Γ.extend A)) (dom : Shape Γ) (k : Nat) (names : Fin k → Σ A : Ty Γ, Tm Γ A)
      (ins outs : Fin k → Shape Γ)
  | lam (k : Nat) (names : Fin k → Σ A : Ty Γ, Tm Γ A) (ins outs : Fin k → Shape Γ)
  | nat
  | zero
  | succ (predName : Σ A : Ty Γ, Tm Γ A) (pred : Shape Γ)
  | id (ty lhs rhs : Shape Γ)

variable {Γ Γ₁ Γ₂ : Ctx} {k : Nat}

namespace Shape

@[match_pattern] abbrev type : Shape Γ := sort true

def map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) : Shape Γ → Shape Γ₁
  | .bot => .bot
  | .sort r => .sort r
  | .forallE label a k names ins outs =>
    .forallE (pi label) (map arg pi a) k (fun i => arg (names i))
      (fun i => map arg pi (ins i)) (fun i => map arg pi (outs i))
  | .lam k names ins outs =>
    .lam k (fun i => arg (names i)) (fun i => map arg pi (ins i))
      (fun i => map arg pi (outs i))
  | .nat => .nat
  | .zero => .zero
  | .succ name a => .succ (arg name) (map arg pi a)
  | .id A a b => .id (map arg pi A) (map arg pi a) (map arg pi b)

end Shape

structure Graph (Γ : Ctx) where
  size : Nat
  names : Fin size → Σ A : Ty Γ, Tm Γ A
  ins : Fin size → Shape Γ
  outs : Fin size → Shape Γ

namespace Graph

variable {Γ Γ₁ Γ₂ : Ctx}

def map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) (g : Graph Γ) : Graph Γ₁ :=
  ⟨g.size, fun i => arg (g.names i), fun i => (g.ins i).map arg pi,
    fun i => (g.outs i).map arg pi⟩

def nil : Graph Γ := ⟨0, Fin.elim0, Fin.elim0, Fin.elim0⟩

def single (label : Σ A : Ty Γ, Tm Γ A) (x y : Shape Γ) : Graph Γ :=
  ⟨1, fun _ => label, fun _ => x, fun _ => y⟩

def append (f g : Graph Γ) : Graph Γ :=
  ⟨f.size + g.size, Fin.append f.names g.names, Fin.append f.ins g.ins, Fin.append f.outs g.outs⟩

@[simp] theorem append_names_left (f g : Graph Γ) (i : Fin f.size) :
    (f.append g).names (Fin.castAdd g.size i) = f.names i := Fin.append_left _ _ i

@[simp] theorem append_names_right (f g : Graph Γ) (i : Fin g.size) :
    (f.append g).names (Fin.natAdd f.size i) = g.names i := Fin.append_right _ _ i

@[simp] theorem append_ins_left (f g : Graph Γ) (i : Fin f.size) :
    (f.append g).ins (Fin.castAdd g.size i) = f.ins i := Fin.append_left _ _ i

@[simp] theorem append_ins_right (f g : Graph Γ) (i : Fin g.size) :
    (f.append g).ins (Fin.natAdd f.size i) = g.ins i := Fin.append_right _ _ i

@[simp] theorem append_outs_left (f g : Graph Γ) (i : Fin f.size) :
    (f.append g).outs (Fin.castAdd g.size i) = f.outs i := Fin.append_left _ _ i

@[simp] theorem append_outs_right (f g : Graph Γ) (i : Fin g.size) :
    (f.append g).outs (Fin.natAdd f.size i) = g.outs i := Fin.append_right _ _ i

theorem map_append (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) (f g : Graph Γ) :
    (f.append g).map arg pi = (f.map arg pi).append (g.map arg pi) := by
  simp [map, append, funext_iff, Fin.forall_fin_add]

end Graph

namespace Shape

variable {Γ : Ctx}

@[match_pattern] abbrev pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (a : Shape Γ) (g : Graph Γ) : Shape Γ :=
  forallE label a g.size g.names g.ins g.outs

@[match_pattern] abbrev abs (g : Graph Γ) : Shape Γ := lam g.size g.names g.ins g.outs

end Shape

end DomainSemantics
