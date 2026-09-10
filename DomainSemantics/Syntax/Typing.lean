/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Extrinsic
import DomainSemantics.Meta.Judgement

@[expose] public section

namespace DomainSemantics

open Term

judgement Raw.Lift' : Lift → List Term → List Term → Prop where

  ──────────────────── refl
  Raw.Lift' .refl Γ Γ

  Raw.Lift' l Γ Γ'
  ──────────────────── skip
  Raw.Lift' (.skip l) Γ (A :: Γ')

  Raw.Lift' l Γ Γ'
  ──────────────────── cons
  Raw.Lift' (.cons l) (A :: Γ) (A.lift' l :: Γ')

judgement Lookup : List Term → Nat → Term → Prop where

  ──────────────────── zero
  Lookup (ty :: Γ) 0 ty.lift

  Lookup Γ n ty
  ──────────────────── succ
  Lookup (A :: Γ) (n + 1) ty.lift

theorem Lookup.weak' (W : Raw.Lift' ρ Γ Γ') (h : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact h
  | skip W ih => have' := (ih h).succ; rwa [Term.lift, ← Term.lift'_comp] at this
  | cons W ih =>
    cases h with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [Term.lift, ← Term.lift'_comp]
    | succ h => refine' cast _ (ih h).succ; congr 1; simp [Term.lift, ← Term.lift'_comp]

theorem Lookup.uniq : Lookup Γ i A → Lookup Γ i B → A = B
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

set_option hygiene false in
scoped notation:65 Γ " ⊢ " e₁:66 " : " A:36 => IsDefEq Γ e₁ e₁ A
set_option hygiene false in
scoped notation:65 Γ " ⊢ " e₁:66 " ≡ " e₂:66 " : " A:36 => IsDefEq Γ e₁ e₂ A

judgement IsDefEq : List Term → Term → Term → Term → Prop where

  Lookup Γ i A
  Γ ⊢ A : .sort u
  ──────────────────── bvar
  Γ ⊢ .bvar i : A

  Γ ⊢ e₁ ≡ e₂ : A
  ──────────────────── symm
  Γ ⊢ e₂ ≡ e₁ : A

  Γ ⊢ e₁ ≡ e₂ : A
  Γ ⊢ e₂ ≡ e₃ : A
  ──────────────────── trans
  Γ ⊢ e₁ ≡ e₃ : A

  Γ ⊢ A ≡ B : .sort u
  Γ ⊢ B ≡ C : .sort v
  ──────────────────── trans'
  Γ ⊢ A ≡ C : .sort u

  ──────────────────── sort
  Γ ⊢ .sort l : .type

  Γ ⊢ A : .sort u
  A :: Γ ⊢ B : .sort v
  Γ ⊢ f ≡ f' : .forallE A B
  Γ ⊢ a ≡ a' : A
  Γ ⊢ B.inst a ≡ B.inst a' : .sort v
  ──────────────────── appDF
  Γ ⊢ .app f a ≡ .app f' a' : B.inst a

  Γ ⊢ A ≡ A' : .sort u
  A :: Γ ⊢ B : .sort v
  A :: Γ ⊢ body ≡ body' : B
  A' :: Γ ⊢ body ≡ body' : B
  Γ ⊢ .forallE A B : .sort v
  ──────────────────── lamDF
  Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B

  Γ ⊢ A ≡ A' : .sort u
  A :: Γ ⊢ body ≡ body' : .sort v
  A' :: Γ ⊢ body ≡ body' : .sort v
  ──────────────────── forallEDF
  Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v

  Γ ⊢ A ≡ B : .sort u
  Γ ⊢ e₁' ≡ e₂' : A
  ──────────────────── defeqDF
  Γ ⊢ e₁' ≡ e₂' : B

  Γ ⊢ A : .sort u
  A :: Γ ⊢ e : B
  Γ ⊢ e' : A
  Γ ⊢ .app (.lam A e) e' : B.inst e'
  Γ ⊢ e.inst e' : B.inst e'
  ──────────────────── beta
  Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'

  Γ ⊢ e : .forallE A B
  Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B
  ──────────────────── eta
  Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B

  ──────────────────── nat
  Γ ⊢ .nat : .type

  ──────────────────── zero
  Γ ⊢ .zero : .nat

  Γ ⊢ n ≡ n' : .nat
  ──────────────────── succDF
  Γ ⊢ .succ n ≡ .succ n' : .nat

  .nat :: Γ ⊢ C ≡ C' : .sort v
  Γ ⊢ M ≡ M' : .nat
  Γ ⊢ a ≡ a' : C.inst .zero
  Γ ⊢ b ≡ b' : .natRecType C
  Γ ⊢ C.inst M ≡ C'.inst M' : .sort v
  ──────────────────── natRecDF
  Γ ⊢ .natRec C M a b ≡ .natRec C' M' a' b' : C.inst M

  .nat :: Γ ⊢ C : .sort v
  Γ ⊢ a : C.inst .zero
  Γ ⊢ b : Term.natRecType C
  Γ ⊢ .natRec C .zero a b : C.inst .zero
  ──────────────────── natRec_zero
  Γ ⊢ .natRec C .zero a b ≡ a : C.inst .zero

  .nat :: Γ ⊢ C : .sort v
  Γ ⊢ n : .nat
  Γ ⊢ a : C.inst .zero
  Γ ⊢ b : Term.natRecType C
  Γ ⊢ .natRec C (.succ n) a b : C.inst (.succ n)
  Γ ⊢ .app (.app b n) (.natRec C n a b) : C.inst (.succ n)
  ──────────────────── natRec_succ
  Γ ⊢ .natRec C (.succ n) a b ≡ .app (.app b n) (.natRec C n a b) : C.inst (.succ n)

  Γ ⊢ A ≡ A' : .sort u
  Γ ⊢ a ≡ a' : A
  Γ ⊢ b ≡ b' : A
  ──────────────────── idDF
  Γ ⊢ .id A a b ≡ .id A' a' b' : .prop

  Γ ⊢ A : .sort u
  Γ ⊢ a ≡ a' : A
  Γ ⊢ .id A a a : .prop
  ──────────────────── reflDF
  Γ ⊢ .refl a ≡ .refl a' : .id A a a

  Γ ⊢ A ≡ A' : .sort u
  Γ ⊢ a ≡ a' : A
  Γ ⊢ b ≡ b' : A
  A :: Γ ⊢ C ≡ C' : .sort v
  A' :: Γ ⊢ C ≡ C' : .sort v
  Γ ⊢ x ≡ x' : C.inst a
  Γ ⊢ h ≡ h' : .id A a b
  Γ ⊢ C.inst b ≡ C'.inst b' : .sort v
  Γ ⊢ .id A a b : .prop
  ──────────────────── trDF
  Γ ⊢ .tr A a b C x h ≡ .tr A' a' b' C' x' h' : C.inst b

  Γ ⊢ A : .sort u
  Γ ⊢ a ≡ b : A
  A :: Γ ⊢ C : .sort v
  Γ ⊢ x : C.inst a
  Γ ⊢ h : .id A a b
  Γ ⊢ .tr A a b C x h : C.inst b
  Γ ⊢ x : C.inst b
  ──────────────────── tr_K
  Γ ⊢ .tr A a b C x h ≡ x : C.inst b

  Γ ⊢ p : .prop
  Γ ⊢ hp₁ : p
  Γ ⊢ hp₂ : p
  ──────────────────── proofIrrel
  Γ ⊢ hp₁ ≡ hp₂ : p

theorem IsDefEq.weak' (W : Raw.Lift' ρ Γ Γ') (h : Γ ⊢ e₁ ≡ e₂ : A) :
    Γ' ⊢ e₁.lift' ρ ≡ e₂.lift' ρ : A.lift' ρ := by
  induction h generalizing ρ Γ' with
    simp -failIfUnchanged [lift'_inst_hi, lift'_natRecType] at *
  | bvar h₁ _ ih => exact .bvar (h₁.weak' W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ W) (ih₂ W)
  | trans' _ _ ih₁ ih₂ => exact .trans' (ih₁ W) (ih₂ W)
  | sort => exact .sort
  | appDF _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ => exact .appDF (ih₁ W) (ih₂ W.cons) (ih₃ W) (ih₄ W) (ih₅ W)
  | lamDF _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ => exact .lamDF (ih₁ W) (ih₂ W.cons) (ih₃ W.cons) (ih₄ W.cons) (ih₅ W)
  | forallEDF _ _ _ ih₁ ih₂ ih₃ => exact .forallEDF (ih₁ W) (ih₂ W.cons) (ih₃ W.cons)
  | defeqDF _ _ ih₁ ih₂ => exact .defeqDF (ih₁ W) (ih₂ W)
  | beta _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ => exact .beta (ih₁ W) (ih₂ W.cons) (ih₃ W) (ih₄ W) (ih₅ W)
  | eta _ _ ih₁ ih₂ =>
    exact cast (by simp [lift, ← lift'_comp])
      (IsDefEq.eta (ih₁ W) (cast (by simp [lift, ← lift'_comp]) (ih₂ W)))
  | nat => exact .nat
  | zero => exact .zero
  | succDF _ ih => exact .succDF (ih W)
  | natRecDF _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ => exact .natRecDF (ih₁ W.cons) (ih₂ W) (ih₃ W) (ih₄ W) (ih₅ W)
  | natRec_zero _ _ _ _ ih₁ ih₂ ih₃ ih₄ => exact .natRec_zero (ih₁ W.cons) (ih₂ W) (ih₃ W) (ih₄ W)
  | natRec_succ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    exact .natRec_succ (ih₁ W.cons) (ih₂ W) (ih₃ W) (ih₄ W) (ih₅ W) (ih₆ W)
  | idDF _ _ _ ih₁ ih₂ ih₃ => exact .idDF (ih₁ W) (ih₂ W) (ih₃ W)
  | reflDF _ _ _ ih₁ ih₂ ih₃ => exact .reflDF (ih₁ W) (ih₂ W) (ih₃ W)
  | trDF _ _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₄' ih₅ ih₆ ih₇ ih₈ =>
    exact .trDF (ih₁ W) (ih₂ W) (ih₃ W) (ih₄ W.cons) (ih₄' W.cons) (ih₅ W) (ih₆ W) (ih₇ W) (ih₈ W)
  | tr_K _ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    exact .tr_K (ih₁ W) (ih₂ W) (ih₃ W.cons) (ih₄ W) (ih₅ W) (ih₆ W) (ih₇ W)
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ => exact .proofIrrel (ih₁ W) (ih₂ W) (ih₃ W)

theorem IsDefEq.hasType (h : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢ e₁ : A ∧ Γ ⊢ e₂ : A :=
  ⟨h.trans h.symm, h.symm.trans h⟩

def IsDefEqType (Γ : List Term) (A B : Term) : Prop := ∃ u, Γ ⊢ A ≡ B : .sort u

scoped syntax:65 term:66 " ⊢ " term:66 " ≡ " term:max &" type" : term
scoped syntax:65 term:66 " ⊢ " term:max &" type" : term

scoped macro_rules
  | `($Γ ⊢ $A ≡ $B type) => `(IsDefEqType $Γ $A $B)
  | `($Γ ⊢ $A type) => `(IsDefEqType $Γ $A $A)

@[app_unexpander IsDefEqType] meta def unexpandIsDefEqType : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $A $B) => if A.raw == B.raw then `($Γ ⊢ $A type) else `($Γ ⊢ $A ≡ $B type)
  | _ => throw ()

theorem IsDefEq.type (h : Γ ⊢ A ≡ B : .sort u) : Γ ⊢ A ≡ B type := ⟨u, h⟩

theorem IsDefEqType.symm (h : Γ ⊢ A ≡ B type) : Γ ⊢ B ≡ A type :=
  let ⟨u, h⟩ := h
  ⟨u, h.symm⟩

theorem IsDefEqType.trans (h₁ : Γ ⊢ A ≡ B type) (h₂ : Γ ⊢ B ≡ C type) : Γ ⊢ A ≡ C type :=
  let ⟨u, h₁⟩ := h₁
  let ⟨_, h₂⟩ := h₂
  ⟨u, h₁.trans' h₂⟩

theorem IsDefEqType.hasType (h : Γ ⊢ A ≡ B type) : Γ ⊢ A type ∧ Γ ⊢ B type :=
  let ⟨u, h⟩ := h
  ⟨⟨u, h.hasType.1⟩, ⟨u, h.hasType.2⟩⟩

judgement Raw.WF : List Term → Prop where

  ──────────────────── nil
  Raw.WF []

  Raw.WF Γ
  Γ ⊢ A : .sort u
  ──────────────────── cons {Γ : List Term} {A : Term} {u : Bool}
  Raw.WF (A :: Γ)

scoped notation:65 "⊢ " Γ:36 => Raw.WF Γ

theorem Raw.WF.lookup {Γ : List Term} {i : Nat} {A : Term} : ⊢ Γ → Lookup Γ i A → Γ ⊢ A type
  | .nil, h => nomatch h
  | .cons _ hA, .zero => ⟨_, hA.weak' (.skip .refl)⟩
  | .cons hΓ _, .succ hl =>
    have ⟨_, hA⟩ := hΓ.lookup hl
    ⟨_, hA.weak' (.skip .refl)⟩

theorem IsDefEq.isType (hΓ : ⊢ Γ) : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ A type
  | .bvar h' _ => hΓ.lookup h'
  | .symm h => isType hΓ h
  | .trans h _ => isType hΓ h
  | .trans' _ _ => ⟨_, .sort⟩
  | .sort => ⟨_, .sort⟩
  | .appDF _ _ _ _ h₅ => ⟨_, h₅.hasType.1⟩
  | .lamDF h₁ h₂ _ _ _ => ⟨_, .forallEDF h₁.hasType.1 h₂ h₂⟩
  | .forallEDF _ _ _ => ⟨_, .sort⟩
  | .defeqDF h₁ _ => ⟨_, h₁.hasType.2⟩
  | .beta _ _ _ h _ => isType hΓ h
  | .eta h _ => isType hΓ h
  | .nat => ⟨_, .sort⟩
  | .zero => ⟨_, .nat⟩
  | .succDF _ => ⟨_, .nat⟩
  | .natRecDF _ _ _ _ h₅ => ⟨_, h₅.hasType.1⟩
  | .natRec_zero _ h _ _ => isType hΓ h
  | .natRec_succ _ _ _ _ _ h => isType hΓ h
  | .idDF _ _ _ => ⟨_, .sort⟩
  | .reflDF _ _ h₃ => ⟨_, h₃⟩
  | .trDF _ _ _ _ _ _ _ h₈ _ => ⟨_, h₈.hasType.1⟩
  | .tr_K _ _ _ _ _ h _ => isType hΓ h
  | .proofIrrel h₁ _ _ => ⟨_, h₁⟩

theorem Subst.lift_r_tail {σ : Subst} {ρ : Lift} :
    (σ.lift_r ρ).tail = σ.tail.lift_r ρ :=
  rfl

set_option hygiene false in
scoped notation:65 Γ₁ " ⊢ " σ₁:66 " ≡ " σ₂:66 " ⊣ " Γ₂:36 => Raw.SubstEq Γ₁ σ₁ σ₂ Γ₂

judgement Raw.SubstEq (Γ₁ : List Term) : Subst → Subst → List Term → Prop where

  ──────────────────── nil
  Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ []

  Γ₁ ⊢ σ₁.tail ≡ σ₂.tail ⊣ Γ₂
  Γ₂ ⊢ A : .sort u
  Γ₁ ⊢ σ₁.head ≡ σ₂.head : A.subst σ₁.tail
  ──────────────────── cons
  Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ A :: Γ₂

theorem Raw.SubstEq.left : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂ → Γ₁ ⊢ σ₁ ≡ σ₁ ⊣ Γ₂
  | .nil => .nil
  | .cons W hA hhead => .cons W.left hA hhead.hasType.1

theorem Raw.SubstEq.lookup (W : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂) :
    Lookup Γ₂ i A → Γ₁ ⊢ σ₁ i ≡ σ₂ i : A.subst σ₁ := by
  intro h
  induction W generalizing i A with
  | nil => nomatch h
  | cons W' hA' hhead ih =>
    cases h with
    | zero =>
      simp [show ∀ (s : Subst), s 0 = s.head from fun _ => rfl, lift_subst]
      exact hhead
    | @succ Γ₃ n ty B h' =>
      simp [show ∀ (s : Subst) n, s (n + 1) = s.tail n from fun _ _ => rfl, lift_subst]
      exact ih h'

theorem Raw.SubstEq.skip (W : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂) :
    B :: Γ₁ ⊢ σ₁.lift_r (.skip .refl) ≡ σ₂.lift_r (.skip .refl) ⊣ Γ₂ := by
  induction W with
  | nil => exact .nil
  | cons _ hA' hhead ih =>
    refine .cons (Subst.lift_r_tail ▸ ih) hA' ?_
    rw [Subst.lift_r_tail]
    simpa [lift'_subst, Subst.head, Subst.lift_r] using hhead.weak' (Raw.Lift'.skip .refl)

theorem Raw.SubstEq.lift (W : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂)
    (hA : Γ₂ ⊢ A : .sort u)
    (hA' : Γ₁ ⊢ A.subst σ₁ : .sort u) :
    A.subst σ₁ :: Γ₁ ⊢ σ₁.lift ≡ σ₂.lift ⊣ A :: Γ₂ := by
  have htail : σ₁.lift.tail = σ₁.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  have htail' : σ₂.lift.tail = σ₂.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  refine .cons (htail ▸ htail' ▸ W.skip) hA ?_
  show A.subst σ₁ :: Γ₁ ⊢ .bvar 0 : A.subst σ₁.lift.tail
  rw [htail]
  rw [show A.subst (σ₁.lift_r (.skip .refl)) = (A.subst σ₁).lift' (.skip .refl) from
    (lift'_subst).symm]
  exact .bvar Lookup.zero (hA'.weak' (.skip .refl))

theorem Raw.SubstEq.id {Γ₁ : List Term} (hΓ₁ : ⊢ Γ₁) : Γ₁ ⊢ .id ≡ .id ⊣ Γ₁ := by
  induction hΓ₁ with
  | nil => exact .nil
  | @cons _ A _ _ hA ih =>
    refine .cons ih.skip hA ?_
    rw [show A.subst Subst.id.tail = A.lift' (.skip .refl) by
      show A.subst (Subst.id.lift_r (.skip .refl)) = _
      rw [← lift'_subst, subst_id]]
    exact .bvar Lookup.zero (hA.weak' (.skip .refl))

theorem Raw.SubstEq.lift_at (W : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂)
    (hA : Γ₂ ⊢ A : .sort u)
    (hX : Γ₁ ⊢ X : .sort u)
    (hAX : Γ₁ ⊢ A.subst σ₁ ≡ X : .sort u) :
    X :: Γ₁ ⊢ σ₁.lift ≡ σ₂.lift ⊣ A :: Γ₂ := by
  have htail : σ₁.lift.tail = σ₁.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  have htail' : σ₂.lift.tail = σ₂.lift_r (.skip .refl) := by
    funext i; simp [Subst.tail, Subst.lift, Subst.lift_r]
  refine .cons (htail ▸ htail' ▸ W.skip) hA ?_
  show X :: Γ₁ ⊢ .bvar 0 : A.subst σ₁.lift.tail
  rw [htail, (lift'_subst).symm]
  exact .defeqDF (hAX.symm.weak' (.skip .refl))
    (.bvar .zero (hX.weak' (.skip .refl)))

theorem IsDefEq.subst {Γ₁ Γ₂ : List Term} {σ₁ σ₂ : Subst} {e₁ e₂ A : Term} (hΓ₁ : ⊢ Γ₁)
    (W : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂) (h : Γ₂ ⊢ e₁ ≡ e₂ : A) :
    Γ₁ ⊢ e₁.subst σ₁ ≡ e₂.subst σ₂ : A.subst σ₁ := by
  suffices ∀ {Γ₁ σ₁ σ₂}, ⊢ Γ₁ → Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂ →
      Γ₁ ⊢ e₁.subst σ₁ ≡ e₁.subst σ₂ : A.subst σ₁ ∧
      Γ₁ ⊢ e₁.subst σ₁ ≡ e₂.subst σ₂ : A.subst σ₁ from (this hΓ₁ W).2
  clear hΓ₁ W Γ₁ σ₁ σ₂
  intro Γ₁ σ₁ σ₂ hΓ₁ W
  induction h generalizing Γ₁ σ₁ σ₂ with
  | bvar h' _ => exact ⟨W.lookup h', W.lookup h'⟩
  | sort => exact ⟨.sort, .sort⟩
  | symm _ ih =>
    have ⟨l, c⟩ := ih hΓ₁ W
    have d := (ih hΓ₁ W.left).2.symm
    exact ⟨d.trans c, d.trans l⟩
  | trans _ _ ih₁ ih₂ =>
    exact ⟨(ih₁ hΓ₁ W).1, (ih₁ hΓ₁ W.left).2.trans (ih₂ hΓ₁ W).2⟩
  | trans' _ _ ih₁ ih₂ =>
    exact ⟨(ih₁ hΓ₁ W).1, (ih₁ hΓ₁ W.left).2.trans' (ih₂ hΓ₁ W).2⟩
  | defeqDF _ _ ih₁ ih₂ =>
    have hAB := (ih₁ hΓ₁ W.left).2
    have ⟨l, c⟩ := ih₂ hΓ₁ W
    exact ⟨.defeqDF hAB l, .defeqDF hAB c⟩
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ =>
    exact ⟨(ih₂ hΓ₁ W).1, .proofIrrel (ih₁ hΓ₁ W.left).1
      (ih₂ hΓ₁ W.left).1 (ih₃ hΓ₁ W).1.hasType.2⟩
  | eta _ _ ih₁ ih₂ =>
    refine ⟨(ih₂ hΓ₁ W).1, .trans ?_ (ih₁ hΓ₁ W).1⟩
    have hη := (ih₂ hΓ₁ W.left).1
    simp [Term.subst, lift_subst_lift, Subst.lift] at hη ⊢
    exact .eta (ih₁ hΓ₁ W.left).1 hη
  | beta hA _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    have hAσ := (ih₁ hΓ₁ W.left).1
    have he := (ih₂ (.cons hΓ₁ hAσ) (W.left.lift hA hAσ)).1
    refine ⟨(ih₄ hΓ₁ W).1, .trans ?_ (ih₅ hΓ₁ W).1⟩
    simpa! [subst_inst] using IsDefEq.beta hAσ he (ih₃ hΓ₁ W.left).1
      (subst_inst ▸ (ih₄ hΓ₁ W.left).1)
      (by simpa [subst_inst] using (ih₅ hΓ₁ W.left).1)
  | @appDF Γ₂ A u B v f f' a a' hA _ _ _ _ ih₁ ih₂ ih₃ ih₄ _ =>
    have hAσ := (ih₁ hΓ₁ W.left).1
    have hBσ := (ih₂ (.cons hΓ₁ hAσ) (W.left.lift hA hAσ)).1
    have hB {x y} (hxy : Γ₁ ⊢ x ≡ y : A.subst σ₁) :
        Γ₁ ⊢ (B.subst σ₁.lift).inst x ≡ (B.subst σ₁.lift).inst y : .sort v := by
      simpa! [inst_lift_cons] using
        (ih₂ hΓ₁ (.cons (σ₁ := σ₁.cons x) (σ₂ := σ₁.cons y) W.left hA hxy)).1
    have ⟨lf, cf⟩ := ih₃ hΓ₁ W
    have ⟨la, ca⟩ := ih₄ hΓ₁ W
    exact subst_inst ▸ ⟨.appDF hAσ hBσ lf la (hB la), .appDF hAσ hBσ cf ca (hB ca)⟩
  | lamDF hA _ _ _ _ ih₁ ih₂ ih₃ _ ih₅ =>
    have ⟨lA, cA⟩ := ih₁ hΓ₁ W
    have hAσ := lA.hasType.1
    have Wl := W.lift hA.hasType.1 hAσ
    have hB := (ih₂ (.cons hΓ₁ hAσ) Wl).1.hasType.1
    have ⟨le, ce⟩ := ih₃ (.cons hΓ₁ hAσ) Wl
    have le' := (ih₃ (.cons hΓ₁ lA.hasType.2)
      (W.lift_at hA.hasType.1 lA.hasType.2 lA)).1
    have ce' := (ih₃ (.cons hΓ₁ cA.hasType.2)
      (W.lift_at hA.hasType.1 cA.hasType.2 cA)).2
    have hF := (ih₅ hΓ₁ W.left).1
    exact ⟨.lamDF lA hB le le' hF, .lamDF cA hB ce ce' hF⟩
  | forallEDF hA _ _ ih₁ ih₂ _ =>
    have ⟨lA, cA⟩ := ih₁ hΓ₁ W
    have hAσ := lA.hasType.1
    have ⟨lB, cB⟩ := ih₂ (.cons hΓ₁ hAσ) (W.lift hA.hasType.1 hAσ)
    have lB' := (ih₂ (.cons hΓ₁ lA.hasType.2)
      (W.lift_at hA.hasType.1 lA.hasType.2 lA)).1
    have cB' := (ih₂ (.cons hΓ₁ cA.hasType.2)
      (W.lift_at hA.hasType.1 cA.hasType.2 cA)).2
    exact ⟨.forallEDF lA lB lB', .forallEDF cA cB cB'⟩
  | nat => exact ⟨.nat, .nat⟩
  | zero => exact ⟨.zero, .zero⟩
  | succDF _ ih => have ⟨l, c⟩ := ih hΓ₁ W; exact ⟨.succDF l, .succDF c⟩
  | @natRecDF Γ₂ C C' v M M' a a' b b' _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    have ⟨lC, cC⟩ := ih₁ (.cons hΓ₁ .nat) (W.lift .nat .nat)
    have ⟨lM, cM⟩ := ih₂ hΓ₁ W
    have ⟨la, ca⟩ := ih₃ hΓ₁ W
    have ⟨lb, cb⟩ := ih₄ hΓ₁ W
    have ⟨lCM, cCM⟩ := ih₅ hΓ₁ W
    simp [subst_inst, subst_natRecType] at la ca lb cb lCM cCM ⊢
    exact ⟨.natRecDF lC lM la lb lCM, .natRecDF cC cM ca cb cCM⟩
  | @natRec_zero Γ₂ C v a b _ _ _ _ ih₁ ih₂ ih₃ ih₄ =>
    refine ⟨(ih₄ hΓ₁ W).1, .trans ?_ (ih₂ hΓ₁ W).1⟩
    exact subst_inst.symm ▸ .natRec_zero
      (ih₁ (.cons hΓ₁ .nat) (W.left.lift .nat .nat)).1
      (subst_inst ▸ (ih₂ hΓ₁ W.left).1 :)
      (subst_natRecType C σ₁ ▸ (ih₃ hΓ₁ W.left).1 :)
      (subst_inst ▸ (ih₄ hΓ₁ W.left).1 :)
  | @natRec_succ Γ₂ C v n a b _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
    refine ⟨(ih₅ hΓ₁ W).1, .trans ?_ (ih₆ hΓ₁ W).1⟩
    rw [subst_inst]
    exact .natRec_succ (ih₁ (.cons hΓ₁ .nat) (W.left.lift .nat .nat)).1
      (ih₂ hΓ₁ W.left).1
      (subst_inst ▸ (ih₃ hΓ₁ W.left).1 :)
      (subst_natRecType C σ₁ ▸ (ih₄ hΓ₁ W.left).1 :)
      (subst_inst ▸ (ih₅ hΓ₁ W.left).1 :)
      (subst_inst ▸ (ih₆ hΓ₁ W.left).1 :)
  | idDF _ _ _ ih₁ ih₂ ih₃ =>
    have ⟨lA, cA⟩ := ih₁ hΓ₁ W
    have ⟨la, ca⟩ := ih₂ hΓ₁ W
    have ⟨lb, cb⟩ := ih₃ hΓ₁ W
    exact ⟨.idDF lA la lb, .idDF cA ca cb⟩
  | reflDF _ _ _ ih₁ ih₂ ih₃ =>
    have hA := (ih₁ hΓ₁ W.left).1
    have hI := (ih₃ hΓ₁ W.left).1
    have ⟨l, c⟩ := ih₂ hΓ₁ W
    exact ⟨.reflDF hA l hI, .reflDF hA c hI⟩
  | trDF hA _ _ _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ _ ih₅ ih₆ ih₇ ih₈ =>
    have ⟨lA, cA⟩ := ih₁ hΓ₁ W
    have hAσ := lA.hasType.1
    have ⟨lC, cC⟩ := ih₄ (.cons hΓ₁ hAσ) (W.lift hA.hasType.1 hAσ)
    have lC' := (ih₄ (.cons hΓ₁ lA.hasType.2)
      (W.lift_at hA.hasType.1 lA.hasType.2 lA)).1
    have cC' := (ih₄ (.cons hΓ₁ cA.hasType.2)
      (W.lift_at hA.hasType.1 cA.hasType.2 cA)).2
    have ⟨la, ca⟩ := ih₂ hΓ₁ W
    have ⟨lb, cb⟩ := ih₃ hΓ₁ W
    have ⟨lx, cx⟩ := ih₅ hΓ₁ W
    have ⟨lh, ch⟩ := ih₆ hΓ₁ W
    have ⟨lCb, cCb⟩ := ih₇ hΓ₁ W
    have hI := (ih₈ hΓ₁ W.left).1
    simp [subst_inst] at lx cx lCb cCb ⊢
    exact ⟨.trDF lA la lb lC lC' lx lh lCb hI, .trDF cA ca cb cC cC' cx ch cCb hI⟩
  | tr_K hA _ _ _ _ _ _ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ ih₇ =>
    have hAσ := (ih₁ hΓ₁ W.left).1
    have hC := (ih₃ (.cons hΓ₁ hAσ) (W.left.lift hA hAσ)).1
    refine ⟨(ih₆ hΓ₁ W).1, .trans ?_ (ih₇ hΓ₁ W).1⟩
    exact subst_inst.symm ▸ .tr_K hAσ (ih₂ hΓ₁ W.left).2 hC
      (subst_inst ▸ (ih₄ hΓ₁ W.left).1 :) (ih₅ hΓ₁ W.left).1
      (subst_inst ▸ (ih₆ hΓ₁ W.left).1 :) (subst_inst ▸ (ih₇ hΓ₁ W.left).1 :)

theorem IsDefEqType.subst {Γ₁ Γ₂ : List Term} {σ₁ σ₂ : Subst} {A B : Term} (hΓ₁ : ⊢ Γ₁)
    (W : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂) (h : Γ₂ ⊢ A ≡ B type) : Γ₁ ⊢ A.subst σ₁ ≡ (B.subst σ₂) type :=
  let ⟨u, h⟩ := h
  ⟨u, h.subst hΓ₁ W⟩

theorem Raw.SubstEq.one (hΓ₁ : ⊢ Γ₁) (h₀ : Γ₁ ⊢ e₀ : A₀) :
    Γ₁ ⊢ Subst.one e₀ ≡ Subst.one e₀ ⊣ A₀ :: Γ₁ :=
  have ⟨_, hA₀⟩ := h₀.isType hΓ₁
  .cons (Raw.SubstEq.id hΓ₁) hA₀ (subst_id ▸ h₀)

theorem IsDefEq.inst0 (hΓ : ⊢ Γ)
    (h₀ : Γ ⊢ e₀ : A₀)
    (h : A₀::Γ ⊢ e₁ ≡ e₂ : A) :
    Γ ⊢ e₁.inst e₀ ≡ e₂.inst e₀ : A.inst e₀ :=
  h.subst hΓ (Raw.SubstEq.one hΓ h₀)

theorem IsDefEq.instDF (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u)
    (hf : A::Γ ⊢ f ≡ f' : B)
    (ha : Γ ⊢ a ≡ a' : A) :
    Γ ⊢ f.inst a ≡ f'.inst a' : B.inst a :=
  hf.subst hΓ (.cons (Raw.SubstEq.id hΓ) hA (subst_id ▸ ha))

theorem lift_cons_skip_inst_bvar0 {X : Term} :
    (X.lift' (.cons (.skip .refl))).inst (.bvar 0) = X := by
  have hsub : (Subst.lift_l (.cons (.skip .refl)) (Subst.one (.bvar 0))) = (Subst.id : Subst) := by
    funext i; cases i <;> rfl
  show (X.lift' (.cons (.skip .refl))).subst (.one (.bvar 0)) = X
  rw [subst_lift', hsub, subst_id]

theorem IsDefEq.defeqDF_l (hΓ : ⊢ Γ)
    (h₁ : Γ ⊢ A ≡ A' : .sort u)
    (h₂ : A::Γ ⊢ e₁ ≡ e₂ : B) : A'::Γ ⊢ e₁ ≡ e₂ : B := by
  have hbvar : A' :: Γ ⊢ .bvar 0 : A.lift :=
    (h₁.weak' (.skip .refl)).symm.defeqDF (.bvar .zero (h₁.hasType.2.weak' (.skip .refl)))
  simpa [lift_cons_skip_inst_bvar0] using
    IsDefEq.inst0 (.cons hΓ h₁.hasType.2) hbvar (h₂.weak' (.cons (.skip .refl)))

theorem IsDefEq.bvar₀ (hΓ : ⊢ Γ) (h : Lookup Γ i A) : Γ ⊢ .bvar i : A :=
  have ⟨_, hA⟩ := hΓ.lookup h; .bvar h hA

theorem IsDefEq.forallEDF₀ (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hbody : A::Γ ⊢ body ≡ body' : .sort v) :
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort v :=
  .forallEDF hA hbody (hA.defeqDF_l hΓ hbody)

theorem IsDefEq.natRecDF₀ (hΓ : ⊢ Γ)
    (hC : .nat::Γ ⊢ C ≡ C' : .sort v)
    (hM : Γ ⊢ M ≡ M' : .nat)
    (ha : Γ ⊢ a ≡ a' : C.inst .zero)
    (hb : Γ ⊢ b ≡ b' : Term.natRecType C) :
    Γ ⊢ .natRec C M a b ≡ .natRec C' M' a' b' : C.inst M :=
  .natRecDF hC hM ha hb (.instDF hΓ .nat hC hM)

theorem IsDefEq.natRecStepDF (hΓ : ⊢ Γ) (hC : .nat::Γ ⊢ C ≡ C' : .sort v) :
    C::.nat::Γ ⊢ Term.natRecStep C ≡ Term.natRecStep C' : .sort v := by
  have hΓn : ⊢ .nat::Γ := .cons hΓ .nat
  have hΓnC : ⊢ C::.nat::Γ := .cons hΓn hC.hasType.1
  have hC' : (Term.nat.lift' (.skip (.skip .refl)))::C::.nat::Γ ⊢
      C.lift' (.cons (.skip (.skip .refl))) ≡ C'.lift' (.cons (.skip (.skip .refl))) : .sort v :=
    hC.weak' (.cons (Γ' := C::.nat::Γ) (.skip (.skip .refl)))
  have hn : C::.nat::Γ ⊢ .succ (.bvar 1) : .nat :=
    .succDF (.bvar₀ hΓnC (Lookup.succ Lookup.zero))
  exact IsDefEq.inst0 hΓnC hn hC'

theorem IsDefEq.natRecStep_ty (hΓ : ⊢ Γ) (hC : .nat::Γ ⊢ C : .sort v) :
    C::.nat::Γ ⊢ Term.natRecStep C : .sort v := .natRecStepDF hΓ hC

theorem IsDefEq.natRecTypeDF (hΓ : ⊢ Γ) (hC : .nat::Γ ⊢ C ≡ C' : .sort v) :
    Γ ⊢ Term.natRecType C ≡ Term.natRecType C' : .sort v :=
  have hΓn : ⊢ .nat::Γ := .cons hΓ .nat
  .forallEDF₀ hΓ .nat (.forallEDF₀ hΓn hC (.natRecStepDF hΓ hC))

end DomainSemantics
