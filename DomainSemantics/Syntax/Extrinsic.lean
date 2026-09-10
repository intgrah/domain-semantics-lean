/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Lift

@[expose] public section

namespace DomainSemantics

inductive Term where
  | bvar (i : Nat)
  | sort (u : Bool)
  | app (f a : Term)
  | lam (A e : Term)
  | forallE (A B : Term)
  | nat
  | zero
  | succ (n : Term)
  | natRec (C M a b : Term)
  | id (A a b : Term)
  | refl (a : Term)
  | tr (A a b C x h : Term)

abbrev Term.type := Term.sort true
abbrev Term.prop := Term.sort false

instance : Inhabited Term := ⟨.prop⟩

namespace Term

@[simp] def lift' : Term → Lift → Term
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)
  | .nat, _ => .nat
  | .zero, _ => .zero
  | .succ n, k => .succ (n.lift' k)
  | .natRec C M a b, k => .natRec (C.lift' k.cons) (M.lift' k) (a.lift' k) (b.lift' k)
  | .id A a b, k => .id (A.lift' k) (a.lift' k) (b.lift' k)
  | .refl a, k => .refl (a.lift' k)
  | .tr A a b C x h, k =>
    .tr (A.lift' k) (a.lift' k) (b.lift' k) (C.lift' k.cons) (x.lift' k) (h.lift' k)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : Term} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : Term} (h : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : Term} : e.lift' .refl = e := lift'_depth_zero rfl

end Term
open Term

variable (C : Term)

def Subst := Nat → Term

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i + 1 => (σ i).lift

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : Term := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n + 1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
def Subst.cons (σ : Subst) (e : Term) : Subst
  | 0 => e
  | i + 1 => σ i

abbrev Subst.one (e : Term) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)
def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

def Term.subst : Term → Subst → Term
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)
  | .nat, _ => .nat
  | .zero, _ => .zero
  | .succ n, σ => .succ (n.subst σ)
  | .natRec C M a b, σ => .natRec (C.subst σ.lift) (M.subst σ) (a.subst σ) (b.subst σ)
  | .id A a b, σ => .id (A.subst σ) (a.subst σ) (b.subst σ)
  | .refl a, σ => .refl (a.subst σ)
  | .tr A a b C x h, σ =>
    .tr (A.subst σ) (a.subst σ) (b.subst σ) (C.subst σ.lift) (x.subst σ) (h.subst σ)

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : Term} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : Term} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : Term} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, Term.lift]
  rw [Term.lift, Term.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : Term} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : Term} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : Term} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

def Term.inst (e a : Term) : Term := e.subst (.one a)

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (h : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear h
    induction n generalizing i with
    | zero => simp
    | succ n ih =>
      cases i with
      | zero => simp
      | succ i => by_cases hni : n ≤ i <;> simp [ih, hni, Nat.add_assoc]
  rw [this]; split <;> simp
  rename_i hni
  have := h (i - n)
  simp [hni] at this
  simp [this]

theorem lift_r_one (e : Term) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : Term) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e₁ e₂ : Term) (ρ : Lift) :
    lift' (e₁.inst e₂) ρ = (lift' e₁ ρ.cons).inst (lift' e₂ ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem lift_lift' {A : Term} {l : Lift} : A.lift.lift' l.cons = (A.lift' l).lift := by
  show (A.lift' (.skip .refl)).lift' l.cons = (A.lift' l).lift' (.skip .refl)
  rw [← lift'_comp, ← lift'_comp]; simp

theorem lift_subst_lift {A : Term} {σ : Subst} : A.lift.subst σ.lift = (A.subst σ).lift := by
  rw [lift_subst, show σ.lift.tail = σ.lift_r (.skip .refl) from by
        funext i; simp [Subst.tail, Subst.lift, Subst.lift_r], ← lift'_subst]

theorem subst_inst {e : Term} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [Term.inst, Term.inst, subst_subst, subst_subst]; congr 1
  funext i; rcases i with _ | i <;> simp [Subst.comp, Subst.lift, Term.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← Term.inst, lift_inst]; rfl

def Term.natRecStep  : Term :=
  (C.lift' (.cons (.skip (.skip .refl)))).inst (.succ (.bvar 1))

def Term.natRecType  : Term := .forallE .nat (.forallE C (Term.natRecStep C))

theorem subst_lift'_cons_skip2 {e : Term} {σ : Subst} :
    (e.lift' (.cons (.skip (.skip .refl)))).subst σ.lift.lift.lift =
    (e.subst σ.lift).lift' (.cons (.skip (.skip .refl))) := by
  rw [subst_lift', lift'_subst]; congr 1
  funext i; cases i with | zero => rfl | succ n
  simp [Subst.lift_l, Subst.lift_r, Subst.lift, Lift.liftVar, lift_lift']
  simp [← lift'_comp]

theorem lift'_natRecStep (ρ : Lift) :
    (Term.natRecStep C).lift' ρ.cons.cons = Term.natRecStep (C.lift' ρ.cons) := by
  simp [Term.natRecStep, lift'_inst_hi, ← lift'_comp]

theorem lift'_natRecType (ρ : Lift) :
    (Term.natRecType C).lift' ρ = Term.natRecType (C.lift' ρ.cons) := by
  simp [natRecType, lift'_natRecStep]

theorem subst_natRecStep (σ : Subst) :
    (Term.natRecStep C).subst σ.lift.lift = Term.natRecStep (C.subst σ.lift) := by
  simp! [Term.natRecStep, subst_inst, subst_lift'_cons_skip2]

theorem subst_natRecType (σ : Subst) :
    (Term.natRecType C).subst σ = Term.natRecType (C.subst σ.lift) := by
  simp! [natRecType, subst_natRecStep]

theorem inst_lift_cons {e : Term} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [Term.inst, subst_subst, Subst.one]; congr 1
  funext i; rcases i with _ | i <;> simp! [Subst.comp, lift_subst_cons]

end DomainSemantics
