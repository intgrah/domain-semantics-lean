/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Autosubst
public import Batteries.Tactic.Alias

@[expose] public section

namespace DomainSemantics

open Autosubst Autosubst.Notation

autosubst
  Term where
    | sort : Bool → Term
    | app : Term → Term → Term
    | lam : Term → (bind Term in Term) → Term
    | forallE : Term → (bind Term in Term) → Term
    | nat : Term
    | zero : Term
    | succ : Term → Term
    | natRec : (bind Term in Term) → Term → Term → Term → Term
    | id : Term → Term → Term → Term
    | refl : Term → Term
    | tr : Term → Term → Term → (bind Term in Term) → Term → Term → Term

@[reducible] alias Term.bvar := Term.var_Term
@[reducible] alias upRen := upRen_Term_Term

abbrev Term.type := Term.sort true
abbrev Term.prop := Term.sort false

instance : Inhabited Term := ⟨.prop⟩

abbrev Subst := Nat → Term

section

open Term

variable {e a x A B C M b h : Term} {σ : Subst} {ξ : Nat → Nat} {i : Nat} {u : Bool}

@[simp] theorem subst_bvar : (bvar i)[σ] = σ i := rfl
@[simp] theorem subst_sort : (sort u)[σ] = sort u := rfl
@[simp] theorem subst_app : (app e a)[σ] = app e[σ] a[σ] := rfl
@[simp] theorem subst_lam : (lam A e)[σ] = lam A[σ] e[⇑σ] := rfl
@[simp] theorem subst_forallE : (forallE A B)[σ] = forallE A[σ] B[⇑σ] := rfl
@[simp] theorem subst_nat : nat[σ] = nat := rfl
@[simp] theorem subst_zero : zero[σ] = zero := rfl
@[simp] theorem subst_succ : (succ e)[σ] = succ e[σ] := rfl
@[simp] theorem subst_natRec : (natRec C M a b)[σ] = natRec C[⇑σ] M[σ] a[σ] b[σ] := rfl
@[simp] theorem subst_identity : (id A a b)[σ] = id A[σ] a[σ] b[σ] := rfl
@[simp] theorem subst_refl : (refl a)[σ] = refl a[σ] := rfl
@[simp] theorem subst_tr : (tr A a b C x h)[σ] = tr A[σ] a[σ] b[σ] C[⇑σ] x[σ] h[σ] := rfl
@[simp] theorem ren_bvar : (bvar i)⟨ξ⟩ = bvar (ξ i) := rfl
@[simp] theorem ren_sort : (sort u)⟨ξ⟩ = sort u := rfl
@[simp] theorem ren_app : (app e a)⟨ξ⟩ = app e⟨ξ⟩ a⟨ξ⟩ := rfl
@[simp] theorem ren_lam : (lam A e)⟨ξ⟩ = lam A⟨ξ⟩ e⟨upRen ξ⟩ := rfl
@[simp] theorem ren_forallE : (forallE A B)⟨ξ⟩ = forallE A⟨ξ⟩ B⟨upRen ξ⟩ := rfl
@[simp] theorem ren_nat : nat⟨ξ⟩ = nat := rfl
@[simp] theorem ren_zero : zero⟨ξ⟩ = zero := rfl
@[simp] theorem ren_succ : (succ e)⟨ξ⟩ = succ e⟨ξ⟩ := rfl
@[simp] theorem ren_natRec : (natRec C M a b)⟨ξ⟩ = natRec C⟨upRen ξ⟩ M⟨ξ⟩ a⟨ξ⟩ b⟨ξ⟩ := rfl
@[simp] theorem ren_identity : (id A a b)⟨ξ⟩ = id A⟨ξ⟩ a⟨ξ⟩ b⟨ξ⟩ := rfl
@[simp] theorem ren_refl : (refl a)⟨ξ⟩ = refl a⟨ξ⟩ := rfl
@[simp] theorem ren_tr : (tr A a b C x h)⟨ξ⟩ = tr A⟨ξ⟩ a⟨ξ⟩ b⟨ξ⟩ C⟨upRen ξ⟩ x⟨ξ⟩ h⟨ξ⟩ := rfl
@[simp] theorem up_zero : ⇑σ 0 = bvar 0 := rfl
@[simp] theorem up_succ : ⇑σ (i + 1) = (σ i)⟨↑⟩ := rfl
@[simp] theorem upRen_zero : upRen ξ 0 = 0 := rfl
@[simp] theorem upRen_succ : upRen ξ (i + 1) = ξ i + 1 := rfl
@[simp] theorem shift_comp_apply {τ : Nat → Term} : (↑ >> τ) i = τ (i + 1) := rfl
@[simp] theorem comp_subst_apply {τ : Subst} : (σ >> [τ]) i = (σ i)[τ] := rfl
@[simp] theorem shift_up : ↑ >> ⇑σ = σ >> ⟨↑⟩ := rfl
@[simp] theorem id_comp_ren : _root_.id >> ξ = ξ := rfl
@[simp] theorem subst_id : e[bvar] = e := instId'_Term e
@[simp] theorem id_lift : ⇑bvar = bvar := by asimp
theorem subst_subst {τ : Subst} : e[σ][τ] = e[σ >> [τ]] := substSubst_Term σ τ e
theorem lift_subst_cons : e⟨↑⟩[a .: σ] = e[σ] := by asimp
theorem lift_inst (e : Term) : e⟨↑⟩[a/] = e := by asimp
theorem lift_subst_lift : e⟨↑⟩[⇑σ] = e[σ]⟨↑⟩ := by asimp
theorem subst_inst : e[a/][σ] = e[⇑σ][a[σ]/] := by asimp
theorem inst_lift_cons : e[⇑σ][x/] = e[x .: σ] := by asimp
theorem ren_inst : e[a/]⟨ξ⟩ = e⟨upRen ξ⟩[a⟨ξ⟩/] := by asimp
theorem ren_lift : e⟨↑⟩⟨upRen ξ⟩ = e⟨ξ⟩⟨↑⟩ := by asimp
theorem ren_up_shift_inst_bvar0 : e⟨upRen ↑⟩[(bvar 0)/] = e := by asimp

variable (C : Term)

abbrev Term.natRecStep : Term := C⟨upRen (↑ >> ↑)⟩[succ (bvar 1)/]
abbrev Term.natRecType : Term := forallE nat (forallE C (natRecStep C))
theorem ren_natRecStep (ξ : Nat → Nat) : (natRecStep C)⟨upRen (upRen ξ)⟩ = natRecStep C⟨upRen ξ⟩ := by unfold upRen; asimp
theorem ren_natRecType (ξ : Nat → Nat) : (natRecType C)⟨ξ⟩ = natRecType C⟨upRen ξ⟩ := by unfold natRecType; asimp
theorem subst_natRecStep (σ : Subst) : (natRecStep C)[⇑⇑σ] = natRecStep C[⇑σ] := by asimp; substify
theorem subst_natRecType (σ : Subst) : (natRecType C)[σ] = natRecType C[⇑σ] := by unfold natRecType; asimp; substify

end

end DomainSemantics
