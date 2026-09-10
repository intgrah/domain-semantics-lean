/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Typing

@[expose] public section

namespace DomainSemantics

theorem Raw.SubstEq.comp {Γ₁ Γ₂ Γ₃ : List Term} {σ₁ σ₂ σ₃ σ₄ : Subst} (hΓ₁ : ⊢ Γ₁)
    (W₁ : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂) : Γ₂ ⊢ σ₃ ≡ σ₄ ⊣ Γ₃ → Γ₁ ⊢ σ₃.comp σ₁ ≡ σ₄.comp σ₂ ⊣ Γ₃
  | .nil => .nil
  | .cons W₂ hA hhead => .cons (comp hΓ₁ W₁ W₂) hA (subst_subst ▸ hhead.subst hΓ₁ W₁)

structure Raw.Hom (Γ₁ Γ : List Term) where
  srcWF : ⊢ Γ₁
  subst : Subst
  typed : Γ₁ ⊢ subst ≡ subst ⊣ Γ

namespace Raw.Hom

@[ext] theorem ext {σ σ₁ : Raw.Hom Γ₁ Γ} (h : σ.subst = σ₁.subst) :
    σ = σ₁ := by
  have ⟨_, σ, _⟩ := σ
  have ⟨_, σ₁, _⟩ := σ₁
  obtain rfl := h
  rfl

def id (hΓ : ⊢ Γ) : Raw.Hom Γ Γ where
  srcWF := hΓ
  subst := Subst.id
  typed := Raw.SubstEq.id hΓ

def comp (σ : Raw.Hom Γ₁ Γ) (σ₁ : Raw.Hom Γ₂ Γ₁) :
    Raw.Hom Γ₂ Γ where
  srcWF := σ₁.srcWF
  subst := σ.subst.comp σ₁.subst
  typed := Raw.SubstEq.comp σ₁.srcWF σ₁.typed σ.typed

def cons (σ : Raw.Hom Γ₁ Γ) (hA : Γ ⊢ A : .sort u)
    (e : Term) (he : Γ₁ ⊢ e : A.subst σ.subst) : Raw.Hom Γ₁ (A :: Γ) where
  srcWF := σ.srcWF
  subst := σ.subst.cons e
  typed := .cons σ.typed hA he

def one (hΓ : ⊢ Γ) (he : Γ ⊢ e : A) : Raw.Hom Γ (A :: Γ) where
  srcWF := hΓ
  subst := Subst.one e
  typed := Raw.SubstEq.one hΓ he

@[simp] theorem id_subst (hΓ : ⊢ Γ) : (id hΓ).subst = Subst.id := rfl

@[simp] theorem comp_subst (σ : Raw.Hom Γ₁ Γ) (σ₁ : Raw.Hom Γ₂ Γ₁) :
    (σ.comp σ₁).subst = σ.subst.comp σ₁.subst := rfl

@[simp] theorem cons_subst (σ : Raw.Hom Γ₁ Γ) (hA : Γ ⊢ A : .sort u)
    (e : Term) (he : Γ₁ ⊢ e : A.subst σ.subst) :
    (σ.cons hA e he).subst = σ.subst.cons e := rfl

@[simp] theorem one_subst (hΓ : ⊢ Γ) (he : Γ ⊢ e : A) :
    (one hΓ he).subst = Subst.one e := rfl

theorem one_comp (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u)
    (he : Γ ⊢ e : A) (σ : Raw.Hom Γ₁ Γ) :
    (one hΓ he).comp σ =
      σ.cons hA (e.subst σ.subst) (he.subst σ.srcWF σ.typed) := by
  ext
  funext i
  cases i <;> simp! [Subst.comp, Subst.cons, Subst.id]

theorem comp_assoc (σ : Raw.Hom Γ₁ Γ) (σ₁ : Raw.Hom Γ₂ Γ₁)
    (σ₂ : Raw.Hom Γ₃ Γ₂) :
    (σ.comp σ₁).comp σ₂ = σ.comp (σ₁.comp σ₂) := by
  ext
  funext i
  simp! [Subst.comp, subst_subst]

theorem id_comp (σ : Raw.Hom Γ₁ Γ) (hΓ : ⊢ Γ) :
    (id hΓ).comp σ = σ := by
  ext
  funext i
  simp [Subst.comp, Subst.id, Term.subst]

theorem comp_id (σ : Raw.Hom Γ₁ Γ) (hΓ₁ : ⊢ Γ₁) :
    σ.comp (id hΓ₁) = σ := by
  ext
  funext i
  simp [Subst.comp]

def lift (σ : Raw.Hom Γ₁ Γ) (hA : Γ ⊢ A : .sort u) :
    Raw.Hom (A.subst σ.subst :: Γ₁) (A :: Γ) where
  srcWF := .cons σ.srcWF (hA.subst σ.srcWF σ.typed)
  subst := σ.subst.lift
  typed := σ.typed.lift hA (hA.subst σ.srcWF σ.typed)

@[simp] theorem lift_subst (σ : Raw.Hom Γ₁ Γ) (hA : Γ ⊢ A : .sort u) :
    (σ.lift hA).subst = σ.subst.lift := rfl

theorem lift_comp_cons (σ : Raw.Hom Γ₁ Γ) (hA : Γ ⊢ A : .sort u)
    (σ₁ : Raw.Hom Γ₂ Γ₁) (e : Term)
    (he : Γ₂ ⊢ e : (A.subst σ.subst).subst σ₁.subst) :
    (σ.lift hA).comp
        (σ₁.cons (hA.subst σ.srcWF σ.typed) e he) =
      (σ.comp σ₁).cons hA e (by simpa [subst_subst] using he) := by
  ext
  funext i
  cases i with
  | zero => rfl
  | succ i => simpa [comp, cons, lift, Subst.comp, Subst.cons, Subst.lift, Term.subst] using lift_subst_cons

end Raw.Hom

theorem Raw.SubstEq.right (hΓ₁ : ⊢ Γ₁) : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂ → Γ₁ ⊢ σ₂ ≡ σ₂ ⊣ Γ₂
  | .nil => .nil
  | .cons W hA hhead => .cons (right hΓ₁ W) hA ((hA.subst hΓ₁ W).defeqDF hhead.hasType.2)

structure Raw.HomEq (Γ₁ Γ : List Term) where
  srcWF : ⊢ Γ₁
  left : Subst
  right : Subst
  typed : Γ₁ ⊢ left ≡ right ⊣ Γ

namespace Raw.HomEq

def leftHom (W : Raw.HomEq Γ₁ Γ) : Raw.Hom Γ₁ Γ where
  srcWF := W.srcWF
  subst := W.left
  typed := W.typed.left

def rightHom (W : Raw.HomEq Γ₁ Γ) : Raw.Hom Γ₁ Γ where
  srcWF := W.srcWF
  subst := W.right
  typed := W.typed.right W.srcWF

def refl (σ : Raw.Hom Γ₁ Γ) : Raw.HomEq Γ₁ Γ where
  srcWF := σ.srcWF
  left := σ.subst
  right := σ.subst
  typed := σ.typed

def id (hΓ : ⊢ Γ) : Raw.HomEq Γ Γ := refl (Raw.Hom.id hΓ)

def comp (W : Raw.HomEq Γ₁ Γ) (V : Raw.HomEq Γ₂ Γ₁) : Raw.HomEq Γ₂ Γ where
  srcWF := V.srcWF
  left := W.left.comp V.left
  right := W.right.comp V.right
  typed := Raw.SubstEq.comp V.srcWF V.typed W.typed

def cons (W : Raw.HomEq Γ₁ Γ) (hA : Γ ⊢ A : .sort u)
    (a b : Term) (hab : Γ₁ ⊢ a ≡ b : A.subst W.left) :
    Raw.HomEq Γ₁ (A :: Γ) where
  srcWF := W.srcWF
  left := W.left.cons a
  right := W.right.cons b
  typed := .cons W.typed hA hab

def one (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u)
    (a b : Term) (hab : Γ ⊢ a ≡ b : A) : Raw.HomEq Γ (A :: Γ) :=
  (id hΓ).cons hA a b (by simpa [id, refl] using hab)

end Raw.HomEq

end DomainSemantics
