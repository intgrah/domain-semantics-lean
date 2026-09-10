/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Inversion
import DomainSemantics.Meta.Judgement

@[expose] public section

open Autosubst Autosubst.Notation

namespace DomainSemantics

variable {M : Term}

judgement CanonCore : List Term → Term → Term → Prop where

  Lookup Γ i A
  ──────────────────── bvar {Γ : List Term} {i : Nat} {A : Term}
  CanonCore Γ (.bvar i) A

  ──────────────────── sort {Γ : List Term} {l : Bool}
  CanonCore Γ (.sort l) .type

  Γ ⊢ f : .forallE A B
  CanonCore Γ f X
  Γ ⊢ .forallE A B ≡ X type
  Γ ⊢ a : A
  CanonCore Γ a Y
  Γ ⊢ A ≡ Y type
  Γ ⊢ B[a/] : .sort v
  ──────────────────── app {Γ : List Term} {f a A B X Y : Term} {v : Bool}
  CanonCore Γ (.app f a) (B[a/])

  Γ ⊢ A : .sort u
  A :: Γ ⊢ b : B
  CanonCore (A :: Γ) b X
  A :: Γ ⊢ B ≡ X type
  Γ ⊢ .forallE A B : .sort v
  ──────────────────── lam {Γ : List Term} {A b B X : Term} {u v : Bool}
  CanonCore Γ (.lam A b) (.forallE A B)

  Γ ⊢ A : .sort u
  A :: Γ ⊢ B : .sort v
  CanonCore (A :: Γ) B X
  A :: Γ ⊢ .sort v ≡ X type
  ──────────────────── forallE {Γ : List Term} {A B X : Term} {u v : Bool}
  CanonCore Γ (.forallE A B) (.sort v)

  ──────────────────── nat {Γ : List Term}
  CanonCore Γ .nat .type

  ──────────────────── zero {Γ : List Term}
  CanonCore Γ .zero .nat

  ──────────────────── succ {Γ : List Term} {n : Term}
  CanonCore Γ (.succ n) .nat

  Γ ⊢ C[M/] : .sort v
  ──────────────────── natRec {Γ : List Term} {C M a b : Term} {v : Bool}
  CanonCore Γ (.natRec C M a b) (C[M/])

  ──────────────────── id {Γ : List Term} {A a b : Term}
  CanonCore Γ (.id A a b) .prop

  Γ ⊢ a : A
  CanonCore Γ a X
  Γ ⊢ A ≡ X type
  Γ ⊢ .id A a a : .prop
  ──────────────────── refl {Γ : List Term} {a A X : Term}
  CanonCore Γ (.refl a) (.id A a a)

  Γ ⊢ C[b/] : .sort v
  ──────────────────── tr {Γ : List Term} {A a b C x h : Term} {v : Bool}
  CanonCore Γ (.tr A a b C x h) (C[b/])

def Canon (Γ : List Term) (e V : Term) : Prop :=
  ∃ X, CanonCore Γ e X ∧ Γ ⊢ V ≡ X type

theorem Canon.conv {Γ : List Term} {e V V' : Term} (h : Γ ⊢ V' ≡ V type) :
    Canon Γ e V → Canon Γ e V'
  | ⟨X, core, hV⟩ => ⟨X, core, h.trans hV⟩

theorem CanonCore.unique {Γ : List Term} {X X' : Term} :
    ⊢ Γ → CanonCore Γ M X → CanonCore Γ M X' → Γ ⊢ X ≡ X' type := by
  intro hΓ h h'
  induction M generalizing Γ X X' with
  | var_Term i =>
    cases h with | bvar hl => cases h' with | bvar hl' =>
    obtain rfl := hl.uniq hl'
    exact hΓ.lookup hl
  | sort _ =>
    cases h with | sort => cases h' with | sort => exact ⟨_, .sort⟩
  | app f a ihf _ =>
    cases h with | app _ hfc hfX ha _ _ _ => cases h' with | app _ hfc' hfX' _ _ _ _ =>
    have ⟨_, hpi⟩ := hfX.trans ((ihf hΓ hfc hfc').trans hfX'.symm)
    have ⟨⟨_, hAA'⟩, ⟨_, hBB'⟩, _⟩ := hpi.forallE_inv hΓ
    exact ⟨_, IsDefEq.instDF hΓ hAA'.hasType.1 hBB' ha⟩
  | lam A b _ ihb =>
    cases h with | lam hA _ hbc hbX _ => cases h' with | lam _ _ hbc' hbX' =>
    have ⟨_, hBB'⟩ := hbX.trans ((ihb (.cons hΓ hA) hbc hbc').trans hbX'.symm)
    exact ⟨_, IsDefEq.forallEDF hA hBB' hBB'⟩
  | forallE A B _ ihB =>
    cases h with | forallE hA _ hBc hBX => cases h' with | forallE _ _ hBc' hBX' =>
    have ⟨_, hvv'⟩ := hBX.trans ((ihB (.cons hΓ hA) hBc hBc').trans hBX'.symm)
    obtain rfl := hvv'.sort_inv (.cons hΓ hA)
    exact ⟨_, .sort⟩
  | nat =>
    cases h with | nat => cases h' with | nat => exact ⟨_, .sort⟩
  | zero =>
    cases h with | zero => cases h' with | zero => exact ⟨_, .nat⟩
  | succ _ _ =>
    cases h with | succ => cases h' with | succ => exact ⟨_, .nat⟩
  | natRec _ _ _ _ _ _ _ _ =>
    cases h with | natRec hC => cases h' with | natRec => exact ⟨_, hC⟩
  | id _ _ _ _ _ _ =>
    cases h with | id => cases h' with | id => exact ⟨_, .sort⟩
  | refl a iha =>
    cases h with | refl ha hac haX _ => cases h' with | refl _ hac' haX' _ =>
    have ⟨_, hAX⟩ := haX.trans ((iha hΓ hac hac').trans haX'.symm)
    exact ⟨_, IsDefEq.idDF hAX ha ha⟩
  | tr _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases h with | tr hC => cases h' with | tr => exact ⟨_, hC⟩

theorem Canon.unique {Γ : List Term} {V V' : Term} (hΓ : ⊢ Γ) :
    Canon Γ M V →  Canon Γ M V' → Γ ⊢ V ≡ V' type
  | ⟨_, c, hV⟩, ⟨_, c', hV'⟩ => hV.trans ((c.unique hΓ c').trans hV'.symm)

theorem IsDefEq.canon {Γ : List Term} {e₁ e₂ V : Term} :
    Γ ⊢ e₁ ≡ e₂ : V →
    ⊢ Γ →
    Canon Γ e₁ V ∧ Canon Γ e₂ V
  | .bvar hl hA, _ => ⟨⟨_, .bvar hl, hA.type⟩, ⟨_, .bvar hl, hA.type⟩⟩
  | .symm h, hΓ =>
    have ⟨c₁, c₂⟩ := h.canon hΓ
    ⟨c₂, c₁⟩
  | .trans h₁ h₂, hΓ => ⟨(h₁.canon hΓ).1, (h₂.canon hΓ).2⟩
  | .trans' h₁ h₂, hΓ =>
    ⟨(h₁.canon hΓ).1, (h₂.canon hΓ).2.conv (Canon.unique hΓ (h₁.canon hΓ).2 (h₂.canon hΓ).1)⟩
  | .sort, _ => ⟨⟨_, .sort, IsDefEq.sort.type⟩, ⟨_, .sort, IsDefEq.sort.type⟩⟩
  | .appDF _ _ hf ha hB', hΓ =>
    have ⟨⟨_, cf, hfX⟩, ⟨_, cf', hfX'⟩⟩ := hf.canon hΓ
    have ⟨⟨_, ca, haY⟩, ⟨_, ca', haY'⟩⟩ := ha.canon hΓ
    ⟨⟨_, .app hf.hasType.1 cf hfX ha.hasType.1 ca haY hB'.hasType.1, hB'.hasType.1.type⟩,
      ⟨_, .app hf.hasType.2 cf' hfX' ha.hasType.2 ca' haY' hB'.hasType.2, hB'.type⟩⟩
  | .lamDF hAA' hB hb hb' hPi, hΓ =>
    have ⟨_, cb, hbX⟩ := (hb.canon (.cons hΓ hAA'.hasType.1)).1
    have ⟨_, cb', hbX'⟩ := (hb'.canon (.cons hΓ hAA'.hasType.2)).2
    have hB' := hAA'.defeqDF_l hΓ hB
    ⟨⟨_, .lam hAA'.hasType.1 hb.hasType.1 cb hbX hPi, hPi.type⟩,
      ⟨_, .lam hAA'.hasType.2 hb'.hasType.2 cb' hbX' (.forallEDF hAA'.hasType.2 hB' hB'),
        (IsDefEq.forallEDF hAA' hB hB').type⟩⟩
  | .forallEDF hAA' hB hB', hΓ =>
    have ⟨_, cB, hBX⟩ := (hB.canon (.cons hΓ hAA'.hasType.1)).1
    have ⟨_, cB', hBX'⟩ := (hB'.canon (.cons hΓ hAA'.hasType.2)).2
    ⟨⟨_, .forallE hAA'.hasType.1 hB.hasType.1 cB hBX, IsDefEq.sort.type⟩,
      ⟨_, .forallE hAA'.hasType.2 hB'.hasType.2 cB' hBX', IsDefEq.sort.type⟩⟩
  | .defeqDF hAB h, hΓ => ⟨(h.canon hΓ).1.conv hAB.symm.type, (h.canon hΓ).2.conv hAB.symm.type⟩
  | .beta _ _ _ h₄ h₅, hΓ => ⟨(h₄.canon hΓ).1, (h₅.canon hΓ).1⟩
  | .eta h₁ h₂, hΓ => ⟨(h₂.canon hΓ).1, (h₁.canon hΓ).1⟩
  | .nat, _ => ⟨⟨_, .nat, IsDefEq.sort.type⟩, ⟨_, .nat, IsDefEq.sort.type⟩⟩
  | .zero, _ => ⟨⟨_, .zero, IsDefEq.nat.type⟩, ⟨_, .zero, IsDefEq.nat.type⟩⟩
  | .succDF _, _ => ⟨⟨_, .succ, IsDefEq.nat.type⟩, ⟨_, .succ, IsDefEq.nat.type⟩⟩
  | .natRecDF _ _ _ _ h₅, _ =>
    ⟨⟨_, .natRec h₅.hasType.1, h₅.hasType.1.type⟩, ⟨_, .natRec h₅.hasType.2, h₅.type⟩⟩
  | .natRec_zero _ h₂ _ h₄, hΓ => ⟨(h₄.canon hΓ).1, (h₂.canon hΓ).1⟩
  | .natRec_succ _ _ _ _ h₅ h₆, hΓ => ⟨(h₅.canon hΓ).1, (h₆.canon hΓ).1⟩
  | .idDF _ _ _, _ => ⟨⟨_, .id, IsDefEq.sort.type⟩, ⟨_, .id, IsDefEq.sort.type⟩⟩
  | .reflDF hA ha h₃, hΓ =>
    have ⟨_, ca, haX⟩ := (ha.canon hΓ).1
    have ⟨_, ca', haX'⟩ := (ha.canon hΓ).2
    ⟨⟨_, .refl ha.hasType.1 ca haX h₃, h₃.type⟩,
      ⟨_, .refl ha.hasType.2 ca' haX' (IsDefEq.idDF hA ha ha).hasType.2, (IsDefEq.idDF hA ha ha).type⟩⟩
  | .trDF _ _ _ _ _ _ _ h₈ _, _ =>
    ⟨⟨_, .tr h₈.hasType.1, h₈.hasType.1.type⟩, ⟨_, .tr h₈.hasType.2, h₈.type⟩⟩
  | .tr_K _ _ _ _ _ h₆ h₇, hΓ => ⟨(h₆.canon hΓ).1, (h₇.canon hΓ).1⟩
  | .proofIrrel _ h₂ h₃, hΓ => ⟨(h₂.canon hΓ).1, (h₃.canon hΓ).1⟩

theorem IsDefEq.type_unique {Γ : List Term} {A B : Term} :
    ⊢ Γ →
    Γ ⊢ M : A →
    Γ ⊢ M : B →
    Γ ⊢ A ≡ B type :=
  fun hΓ h₁ h₂ => Canon.unique hΓ (h₁.canon hΓ).1 (h₂.canon hΓ).1

theorem IsDefEq.sort_unique {Γ : List Term} {u v : Bool} :
    ⊢ Γ →
    Γ ⊢ M : .sort u →
    Γ ⊢ M : .sort v →
    u = v :=
  fun hΓ h₁ h₂ => have ⟨_, h⟩ := type_unique hΓ h₁ h₂; h.sort_inv hΓ

end DomainSemantics
