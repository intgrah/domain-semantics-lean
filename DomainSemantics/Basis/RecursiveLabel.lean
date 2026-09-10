/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Comprehension.Pullback

public noncomputable section

open Autosubst Autosubst.Notation

namespace DomainSemantics.Tm

open CategoryTheory Opposite

variable {Γ Γ₁ Γ₂ : Ctx} {C C' a a' b b' : Term} {v v' w : Bool}

namespace natRec

theorem substMotive (hC : .nat :: Γ₁ ⊢ C ≡ C' : .sort v)
    (σ₁ : Raw.Hom Γ₂ Γ₁) :
    .nat :: Γ₂ ⊢ C[⇑σ₁.subst] ≡ C'[⇑σ₁.subst] : .sort v := by
  simpa! using hC.subst (.cons σ₁.srcWF .nat) (σ₁.typed.lift .nat .nat)

theorem substZero {C a a' : Term} (ha : Γ₁ ⊢ a ≡ a' : C[Term.zero/])
    (σ₁ : Raw.Hom Γ₂ Γ₁) :
    Γ₂ ⊢ a[σ₁.subst] ≡ a'[σ₁.subst] : (C[⇑σ₁.subst])[Term.zero/] := by
  simpa! [subst_inst] using ha.subst σ₁.srcWF σ₁.typed

theorem substStep {C b b' : Term} (hb : Γ₁ ⊢ b ≡ b' : Term.natRecType C)
    (σ₁ : Raw.Hom Γ₂ Γ₁) :
    Γ₂ ⊢ b[σ₁.subst] ≡ b'[σ₁.subst] :
      Term.natRecType (C[⇑σ₁.subst]) := by
  simpa [↓subst_natRecType] using hb.subst σ₁.srcWF σ₁.typed

end natRec

def natRec (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C) :
    yoneda.obj (Γ.extension (.nat : Γ.as.terms ⊢ .nat : .type)) ⟶ presheaf :=
  let π := Ctx.projectionRaw Γ (.nat : Γ.as.terms ⊢ .nat : .type)
  let hn : .nat :: Γ.as.terms ⊢ .bvar 0 : .nat := .bvar .zero .nat
  yonedaEquiv.symm (pairOfTyping (.cons Γ.as.wf .nat)
    (IsDefEq.inst0 (.cons Γ.as.wf .nat) hn (natRec.substMotive hC π))
    (IsDefEq.natRecDF₀ (.cons Γ.as.wf .nat) (natRec.substMotive hC π) hn
      (natRec.substZero ha π) (natRec.substStep hb π)))

namespace natRec

@[simp] theorem app_ofTerm (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (hn : Γ.as.terms ⊢ n : .nat) :
    (natRec hC ha hb).app (op Γ) (Raw.ContextSection.ofTerm .nat hn).hom =
      pairOfTyping Γ.as.wf (IsDefEq.inst0 Γ.as.wf hn hC)
        (IsDefEq.natRecDF₀ Γ.as.wf hC hn ha hb) := by
  simp only [natRec]
  erw [map_ofTyping]
  congr 1 <;> simp! [Ctx.projectionRaw, Raw.ContextSection.ofTerm, Raw.Hom.one]
  · asimp
  · asimp
    trivial

theorem congr {hC : .nat :: Γ.as.terms ⊢ C : .sort v}
    {hC' : .nat :: Γ.as.terms ⊢ C' : .sort v'}
    {ha : Γ.as.terms ⊢ a : C[Term.zero/]} {ha' : Γ.as.terms ⊢ a' : C'[Term.zero/]}
    {hb : Γ.as.terms ⊢ b : Term.natRecType C} {hb' : Γ.as.terms ⊢ b' : Term.natRecType C'}
    (hCC' : .nat :: Γ.as.terms ⊢ C ≡ C' : .sort w)
    (haa' : Γ.as.terms ⊢ a ≡ a' : C[Term.zero/])
    (hbb' : Γ.as.terms ⊢ b ≡ b' : Term.natRecType C) :
    natRec hC ha hb = natRec hC' ha' hb' := by
  apply yonedaEquiv.injective
  simp only [natRec, Equiv.apply_symm_apply]
  let π := Ctx.projectionRaw Γ (.nat : Γ.as.terms ⊢ .nat : .type)
  have hn : .nat :: Γ.as.terms ⊢ .bvar 0 : .nat := .bvar .zero .nat
  exact pairOfTyping_eq (IsDefEq.instDF (.cons Γ.as.wf .nat) .nat (substMotive hCC' π) hn).type
    (IsDefEq.natRecDF₀ (.cons Γ.as.wf .nat) (substMotive hCC' π) hn (substZero haa' π) (substStep hbb' π))

theorem subst (hC : .nat :: Γ.as.terms ⊢ C : .sort v)
    (ha : Γ.as.terms ⊢ a : C[Term.zero/]) (hb : Γ.as.terms ⊢ b : Term.natRecType C)
    (σ : Γ₁.as ⟶ Γ.as) :
    yoneda.map (Ctx.extensionMap .nat σ) ≫ natRec hC ha hb =
      natRec (substMotive hC σ) (substZero ha σ) (substStep hb σ) := by
  apply yonedaEquiv.injective
  simp only [natRec, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  erw [map_ofTyping, Equiv.apply_symm_apply]
  congr 1 <;> simp! [Ctx.projectionRaw]
  · asimp
    substify
  · asimp
    substify
    trivial

end natRec

end DomainSemantics.Tm
