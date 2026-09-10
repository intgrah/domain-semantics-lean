/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Syntax.Substitution
public import DomainSemantics.Presheaf.Comprehension
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Data.Quot
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Logic.Equiv.Sum

public noncomputable section

open Autosubst Autosubst.Notation

namespace DomainSemantics

open CategoryTheory Opposite

theorem Raw.SubstEq.symm (hΓ₁ : ⊢ Γ₁) : Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂ → Γ₁ ⊢ σ₂ ≡ σ₁ ⊣ Γ₂
  | .nil => .nil
  | .cons W hA hhead =>
    .cons (symm hΓ₁ W) hA ((hA.subst hΓ₁ W).defeqDF hhead.symm)

theorem Raw.SubstEq.trans (hΓ₁ : ⊢ Γ₁) :
    Γ₁ ⊢ σ₁ ≡ σ₂ ⊣ Γ₂ → Γ₁ ⊢ σ₂ ≡ σ₃ ⊣ Γ₂ → Γ₁ ⊢ σ₁ ≡ σ₃ ⊣ Γ₂
  | .nil, .nil => .nil
  | .cons W₁ hA h₁, .cons W₂ _ h₂ =>
    .cons (trans hΓ₁ W₁ W₂) hA (h₁.trans ((hA.subst hΓ₁ W₁).symm.defeqDF h₂))

@[expose] def Raw.HomEq.symm (W : Raw.HomEq Γ₁ Γ₂) : Raw.HomEq Γ₁ Γ₂ where
  srcWF := W.srcWF
  left := W.right
  right := W.left
  typed := W.typed.symm W.srcWF

structure RawCtx where
  terms : List Term
  wf : ⊢ terms

namespace RawCtx

instance category : Category RawCtx where
  Hom Γ₁ Γ₂ := Raw.Hom Γ₁.terms Γ₂.terms
  id Γ₂ := Raw.Hom.id Γ₂.wf
  comp σ₁ σ₂ := σ₂.comp σ₁
  id_comp σ := Raw.Hom.comp_id σ _
  comp_id σ := Raw.Hom.id_comp σ _
  assoc σ₁ σ₂ σ₃ := (Raw.Hom.comp_assoc σ₃ σ₂ σ₁).symm

@[simp] theorem comp_subst {Γ₁ Γ₂ Γ₃ : RawCtx} (σ₁ : Γ₁ ⟶ Γ₂) (σ₂ : Γ₂ ⟶ Γ₃) :
    (σ₁ ≫ σ₂).subst = (σ₂.subst >> [σ₁.subst]) := by rfl

@[expose] def homRel : HomRel RawCtx := fun {Γ₁ Γ₂} σ₁ σ₂ =>
  Γ₁.terms ⊢ σ₁.subst ≡ σ₂.subst ⊣ Γ₂.terms

instance : Congruence homRel where
  equivalence {Γ₁ _} :=
    ⟨fun σ₁ => σ₁.typed, Raw.SubstEq.symm Γ₁.wf, Raw.SubstEq.trans Γ₁.wf⟩
  comp_left {_ _ _} σ₁ {_ _} h := Raw.SubstEq.comp σ₁.srcWF σ₁.typed h
  comp_right {Γ₁ _ _ _ _} σ₂ h := Raw.SubstEq.comp Γ₁.wf h σ₂.typed

end RawCtx

abbrev Ctx := Quotient RawCtx.homRel

abbrev RawCtx.toCtx : RawCtx ⥤ Ctx := Quotient.functor homRel

theorem RawCtx.toCtx_map_eq_iff {Γ Δ : RawCtx} (σ τ : Γ ⟶ Δ) :
    toCtx.map σ = toCtx.map τ ↔ Γ.terms ⊢ σ.subst ≡ τ.subst ⊣ Δ.terms :=
  Quotient.functor_map_eq_iff homRel σ τ

instance : Coe Ctx (List Term) := ⟨fun Γ => Γ.as.terms⟩

@[expose, implicit_reducible] def Ctx.extension (Γ : Ctx) (hA : Γ.as.terms ⊢ A : .sort u) : Ctx :=
  ⟨A :: Γ.as.terms, .cons Γ.as.wf hA⟩

private structure Ty.Repr (Γ : Ctx) where
  term : Term
  wf : Γ.as.terms ⊢ term type

namespace Ty.Repr

private instance setoid (Γ : Ctx) : Setoid (Repr Γ) where
  r A B := Γ.as.terms ⊢ A.term ≡ B.term type
  iseqv := ⟨fun A => A.wf, IsDefEqType.symm, IsDefEqType.trans⟩

end Ty.Repr

private def Ty.Element (Γ : Ctx) := Quotient (Ty.Repr.setoid Γ)

namespace Ty.Element

variable {Γ Δ Θ : Ctx}

private def ofRepr (A : Repr Γ) : Element Γ := ⟦A⟧

@[simp] private theorem ofRepr_eq_iff (A B : Repr Γ) :
    ofRepr A = ofRepr B ↔ Γ.as.terms ⊢ A.term ≡ B.term type :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := Repr.setoid Γ) h⟩

private def reindex (σ : Raw.Hom Δ.as.terms Γ.as.terms) : Element Γ → Element Δ :=
  fun A => Quotient.map (sa := Repr.setoid Γ) (sb := Repr.setoid Δ)
    (fun A => ⟨A.term[σ.subst],
    A.wf.subst σ.srcWF σ.typed⟩) (fun _ _ h => h.subst σ.srcWF σ.typed) A

@[simp] private theorem reindex_ofRepr (σ : Raw.Hom Δ.as.terms Γ.as.terms) (A : Repr Γ) :
    reindex σ (ofRepr A) = ofRepr ⟨A.term[σ.subst],
      A.wf.subst σ.srcWF σ.typed⟩ := rfl

@[simp] private theorem reindex_id (A : Element Γ) (hΓ : ⊢ Γ.as.terms) :
    reindex (Raw.Hom.id hΓ) A = A := by
  obtain ⟨A⟩ := A
  apply (ofRepr_eq_iff _ _).mpr
  change IsDefEqType Γ.as.terms (A.term[(Raw.Hom.id hΓ).subst]) A.term
  simpa [Raw.Hom.id] using A.wf

private theorem reindex_comp (A : Element Γ) (σ : Raw.Hom Δ.as.terms Γ.as.terms)
    (τ : Raw.Hom Θ.as.terms Δ.as.terms) :
    reindex τ (reindex σ A) = reindex (σ.comp τ) A := by
  obtain ⟨A⟩ := A
  apply (ofRepr_eq_iff _ _).mpr
  change IsDefEqType Θ.as.terms ((A.term[σ.subst])[τ.subst])
    (A.term[(σ.comp τ).subst])
  simpa [Raw.Hom.comp, subst_subst] using
    A.wf.subst (σ.comp τ).srcWF (σ.comp τ).typed

private theorem reindex_eq_of_homEq (A : Element Γ) (W : Raw.HomEq Δ.as.terms Γ.as.terms) :
    reindex W.leftHom A = reindex W.rightHom A := by
  obtain ⟨A⟩ := A
  exact (ofRepr_eq_iff _ _).mpr (A.wf.subst W.srcWF W.typed)

end Ty.Element

@[implicit_reducible] def Ty.universe : Ctxᵒᵖ ⥤ Type where
  obj Γ := Ty.Element Γ.unop
  map {Γ Δ} σ := ↾Quot.lift (fun σ : Δ.unop.as ⟶ Γ.unop.as => Ty.Element.reindex σ)
    (fun σ τ h => funext fun A => Ty.Element.reindex_eq_of_homEq A
      ⟨Δ.unop.as.wf, σ.subst, τ.subst, (HomRel.compClosure_iff_self RawCtx.homRel σ τ).mp h⟩) σ.unop
  map_id Γ := ConcreteCategory.hom_ext _ _ (Ty.Element.reindex_id · Γ.unop.as.wf)
  map_comp := by
    rintro _ _ _ ⟨σ⟩ ⟨τ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    obtain ⟨τ, rfl⟩ := RawCtx.toCtx.map_surjective τ
    exact ConcreteCategory.hom_ext _ _ fun A => (Ty.Element.reindex_comp A σ τ).symm

abbrev Ty (Γ : Ctx) := yoneda.obj Γ ⟶ Ty.universe

namespace Ty

variable {Γ Δ Θ : Ctx}

@[expose, implicit_reducible] def presheaf : Ctxᵒᵖ ⥤ Type := yoneda.op ⋙ yoneda.obj Ty.universe

private def ofRepr (A : Repr Γ) : Ty Γ := yonedaEquiv.symm (Element.ofRepr A)

def ofTyping {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) : Ty ⟨Γ, hΓ⟩ :=
  ofRepr ⟨A, hA.type⟩

@[simp] private theorem ofRepr_eq_iff (A B : Repr Γ) :
    ofRepr A = ofRepr B ↔ Γ.as.terms ⊢ A.term ≡ B.term type := by
  rw [ofRepr, ofRepr, yonedaEquiv.symm.injective.eq_iff, Element.ofRepr_eq_iff]

private theorem heq_of_ctx_eq (hctx : Γ = Δ)
    (A : Repr Γ) (B : Repr Δ) (h : Γ.as.terms ⊢ A.term ≡ B.term type) :
    ofRepr A ≍ ofRepr B := by
  cases hctx
  exact heq_of_eq ((ofRepr_eq_iff _ _).mpr h)

private theorem exact_heq (hctx : Γ = Δ)
    (A : Repr Γ) (B : Repr Δ) (h : ofRepr A ≍ ofRepr B) :
    Γ.as.terms ⊢ A.term ≡ B.term type := by
  cases hctx
  exact (ofRepr_eq_iff _ _).mp (eq_of_heq h)

theorem ofTyping_eq_iff {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u)
    (hB : Γ ⊢ B : .sort v) :
    ofTyping hΓ hA = ofTyping hΓ hB ↔ Γ ⊢ A ≡ B type :=
  ofRepr_eq_iff _ _

private noncomputable def repr (A : Ty Γ) : Repr Γ := Quotient.out (yonedaEquiv A)

@[simp] private theorem ofRepr_repr (A : Ty Γ) : ofRepr A.repr = A := by
  apply yonedaEquiv.injective
  rw [ofRepr, Equiv.apply_symm_apply]
  exact Quotient.out_eq (yonedaEquiv A)

private theorem repr_eq (A : Repr Γ) : Γ.as.terms ⊢ A.term ≡ (ofRepr A).repr.term type :=
  (ofRepr_eq_iff _ _).mp (ofRepr_repr (ofRepr A)).symm

private def reindex (σ : Raw.Hom Δ.as.terms Γ.as.terms) (A : Ty Γ) : Ty Δ :=
  yoneda.map (RawCtx.toCtx.map σ) ≫ A

@[simp] private theorem reindex_ofRepr (σ : Raw.Hom Δ.as.terms Γ.as.terms) (A : Repr Γ) :
    reindex σ (ofRepr A) = ofRepr ⟨A.term[σ.subst], A.wf.subst σ.srcWF σ.typed⟩ :=
  yonedaEquiv_symm_naturality_left _ _ _

@[simp] theorem map_ofTyping (hA : Γ.as.terms ⊢ A : .sort u)
    (σ : Raw.Hom Δ.as.terms Γ.as.terms) :
    yoneda.map (RawCtx.toCtx.map σ) ≫ ofTyping Γ.as.wf hA =
      ofTyping Δ.as.wf (hA.subst σ.srcWF σ.typed) :=
  reindex_ofRepr σ ⟨A, hA.type⟩

end Ty

noncomputable def Ctx.extend (Γ : Ctx) (A : Ty Γ) : Ctx :=
  Γ.extension (Ty.repr A).wf.choose_spec

variable {Γ Γ₁ Γ₂ Δ Θ : Ctx}

theorem IsDefEq.convCtxHead {Γ : List Term} (hΓ : ⊢ Γ) (hAA' : Γ ⊢ A ≡ A' : .sort u)
    (h : A :: Γ ⊢ M ≡ N : T) : A' :: Γ ⊢ M ≡ N : T :=
  hAA'.defeqDF_l hΓ h

private theorem Raw.SubstEq.convCtxHead {Γ Δ : List Term} (hΓ : ⊢ Γ) (h : Γ ⊢ A ≡ B type) :
    A :: Γ ⊢ σ ≡ τ ⊣ Δ → B :: Γ ⊢ σ ≡ τ ⊣ Δ
  | .nil => .nil
  | .cons W hC he => .cons (convCtxHead hΓ h W) hC (IsDefEq.convCtxHead hΓ h.choose_spec he)

private def Raw.Hom.convert {Γ : List Term} (hΓ : ⊢ Γ) (h : Γ ⊢ A ≡ B type) : Raw.Hom (B :: Γ) (A :: Γ) where
  srcWF := .cons hΓ h.choose_spec.hasType.2
  subst := Term.bvar
  typed := by
    obtain ⟨u, h⟩ := h
    simpa using (Raw.SubstEq.id hΓ).lift_at h.hasType.1 h.hasType.2 (by simpa using h)

noncomputable def Ctx.extensionIso (hA : Γ.as.terms ⊢ A : .sort u) :
    Γ.extend (Ty.ofTyping Γ.as.wf hA) ≅ Γ.extension hA where
  hom := RawCtx.toCtx.map (Raw.Hom.convert Γ.as.wf (Ty.repr_eq ⟨A, hA.type⟩))
  inv := RawCtx.toCtx.map (Raw.Hom.convert Γ.as.wf (Ty.repr_eq ⟨A, hA.type⟩).symm)
  hom_inv_id := by
    erw [← RawCtx.toCtx.map_comp, ← RawCtx.toCtx.map_id]
    congr 1
  inv_hom_id := by
    erw [← RawCtx.toCtx.map_comp, ← RawCtx.toCtx.map_id]
    congr 1

namespace Ty

private theorem map_extensionIso (hA : Γ.as.terms ⊢ A : .sort u) (B : Ty (Γ.extension hA)) :
    Ty.presheaf.map (Ctx.extensionIso hA).hom.op B =
      reindex (Raw.Hom.convert Γ.as.wf (repr_eq ⟨A, hA.type⟩)) B := rfl

private theorem repr_reindex (A : Ty Γ) (σ : Raw.Hom Δ.as.terms Γ.as.terms) :
    Δ ⊢ A.repr.term[σ.subst] ≡ (reindex σ A).repr.term type := by
  have h := reindex_ofRepr σ A.repr
  rw [ofRepr_repr] at h
  rw [h]
  exact repr_eq (Γ := Δ) ⟨A.repr.term[σ.subst], A.repr.wf.subst σ.srcWF σ.typed⟩

end Ty

private noncomputable def Ctx.liftRaw (σ : Raw.Hom Δ.as.terms Γ.as.terms) (A : Ty Γ) :
    Raw.Hom (Δ.extend (Ty.reindex σ A)).as.terms (Γ.extend A).as.terms where
  srcWF := (Δ.extend (Ty.reindex σ A)).as.wf
  subst := ⇑σ.subst
  typed := by
    obtain ⟨u, h⟩ := Ty.repr_reindex A σ
    obtain ⟨v, hA⟩ := A.repr.wf
    exact Raw.SubstEq.convCtxHead σ.srcWF h.type (σ.typed.lift hA (hA.subst σ.srcWF σ.typed))

namespace Ty

private noncomputable def reindexPair (σ : Raw.Hom Γ₁.as.terms Γ₂.as.terms)
    (a : Σ A : Ty Γ₂, Ty (Γ₂.extend A)) : Σ A : Ty Γ₁, Ty (Γ₁.extend A) :=
  ⟨reindex σ a.1, reindex (Ctx.liftRaw σ a.1) a.2⟩

noncomputable def pairOfTyping {Γ : List Term} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v) :
    Σ A : Ty ⟨Γ, hΓ⟩, Ty ((RawCtx.toCtx.obj ⟨Γ, hΓ⟩).extend A) :=
  ⟨ofTyping hΓ hA, Ty.presheaf.map (Ctx.extensionIso hA).hom.op (ofTyping (.cons hΓ hA) hB)⟩

private theorem reindex_convert_ofRepr {Γ : List Term} (hΓ : ⊢ Γ) (h : Γ ⊢ A ≡ B type)
    (C : Repr (Ctx.extension ⟨Γ, hΓ⟩ h.choose_spec.hasType.1)) :
    reindex (Raw.Hom.convert hΓ h) (ofRepr C) =
      ofRepr (Γ := Ctx.extension ⟨Γ, hΓ⟩ h.choose_spec.hasType.2)
        ⟨C.term, ⟨C.wf.choose, IsDefEq.convCtxHead hΓ h.choose_spec C.wf.choose_spec⟩⟩ := by
  rw [reindex_ofRepr]
  apply (ofRepr_eq_iff _ _).mpr
  change B :: Γ ⊢ C.term[Term.bvar] ≡ C.term type
  simpa [Raw.Hom.convert] using
    C.wf.subst (Raw.Hom.convert hΓ h).srcWF (Raw.Hom.convert hΓ h).typed

theorem pairOfTyping_eq_iff {Γ : List Term} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hA' : Γ ⊢ A' : .sort u') (hB' : A' :: Γ ⊢ B' : .sort v') :
    pairOfTyping hΓ hA hB = pairOfTyping hΓ hA' hB' ↔
      Γ ⊢ A ≡ A' type ∧ A :: Γ ⊢ B ≡ B' type ∧ A' :: Γ ⊢ B ≡ B' type := by
  unfold pairOfTyping
  erw [map_extensionIso, map_extensionIso]
  unfold ofTyping
  erw [reindex_convert_ofRepr, reindex_convert_ofRepr]
  constructor
  · intro h
    have hd := (ofRepr_eq_iff _ _).mp (congrArg Sigma.fst h)
    have hb := exact_heq (congrArg (fun A : Ty ⟨Γ, hΓ⟩ => (RawCtx.toCtx.obj ⟨Γ, hΓ⟩).extend A)
      (congrArg Sigma.fst h)) _ _ (Sigma.mk.inj h).2
    obtain ⟨w, ha⟩ := repr_eq (Γ := ⟨Γ, hΓ⟩) ⟨A, hA.type⟩
    obtain ⟨v, hb⟩ := hb
    have hb := IsDefEq.convCtxHead hΓ ha.symm hb
    exact ⟨hd, hb.type, (IsDefEq.convCtxHead hΓ hd.choose_spec hb).type⟩
  · intro ⟨hd, hb, _⟩
    apply Sigma.ext ((ofRepr_eq_iff _ _).mpr hd)
    apply heq_of_ctx_eq (congrArg (fun A : Ty ⟨Γ, hΓ⟩ => (RawCtx.toCtx.obj ⟨Γ, hΓ⟩).extend A)
      ((ofRepr_eq_iff _ _).mpr hd))
    exact ⟨hb.choose, IsDefEq.convCtxHead hΓ (repr_eq (Γ := ⟨Γ, hΓ⟩) ⟨A, hA.type⟩).choose_spec hb.choose_spec⟩

theorem pairOfTyping_congr {Γ : List Term} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (hB : A :: Γ ⊢ B ≡ B' : .sort v)
    (hB' : A' :: Γ ⊢ B ≡ B' : .sort v) :
    pairOfTyping hΓ hA.hasType.1 hB.hasType.1 =
      pairOfTyping hΓ hA.hasType.2 hB'.hasType.2 :=
  (pairOfTyping_eq_iff _ _ _ _ _).mpr ⟨hA.type, hB.type, hB'.type⟩

theorem pairOfTyping_congrWitness {Γ : List Term} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A : .sort u) (hB : A :: Γ ⊢ B : .sort v)
    (hA' : Γ ⊢ A : .sort u') (hB' : A :: Γ ⊢ B : .sort v') :
    pairOfTyping hΓ hA hB = pairOfTyping hΓ hA' hB' :=
  (pairOfTyping_eq_iff _ _ _ _ _).mpr ⟨hA.type, hB.type, hB.type⟩

end Ty

private structure Tm.Repr (Γ : Ctx) where
  ty : Term
  val : Term
  tyWF : Γ ⊢ ty type
  valWF : Γ ⊢ val : ty

namespace Tm.Repr

private def ofTyping {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) :
    Tm.Repr ⟨Γ, hΓ⟩ where
  ty := A
  val := a
  tyWF := hA.type
  valWF := ha

private instance setoid (Γ : Ctx) : Setoid (Tm.Repr Γ) where
  r p q := Γ ⊢ p.ty ≡ q.ty type ∧ Γ ⊢ p.val ≡ q.val : p.ty
  iseqv := {
    refl p := ⟨p.tyWF, p.valWF⟩
    symm | ⟨⟨u, hty⟩, hval⟩ => ⟨⟨u, hty.symm⟩, hty.defeqDF hval.symm⟩
    trans := fun ⟨⟨_, hpqTy⟩, hpqVal⟩ ⟨hqrTy, hqrVal⟩ =>
      ⟨hpqTy.type.trans hqrTy, hpqVal.trans (hpqTy.symm.defeqDF hqrVal)⟩
    }

private def reindex (p : Tm.Repr Γ) (σ : Raw.Hom Γ₁.as.terms Γ.as.terms) : Tm.Repr Γ₁ where
  ty := p.ty[σ.subst]
  val := p.val[σ.subst]
  tyWF := p.tyWF.subst σ.srcWF σ.typed
  valWF := p.valWF.subst σ.srcWF σ.typed

end Tm.Repr

private def Tm.Class (Γ : Ctx) := Quotient (Tm.Repr.setoid Γ)

private def Tm.type : Tm.Class Γ → Ty.Element Γ :=
  Quotient.lift (fun p => Ty.Element.ofRepr ⟨p.ty, p.tyWF⟩)
    (fun _ _ h => (Ty.Element.ofRepr_eq_iff _ _).mpr h.1)

namespace Tm.Class

private def reindex (σ : Raw.Hom Γ₁.as.terms Γ.as.terms) (a : Class Γ) : Class Γ₁ :=
  Quotient.map (sa := Repr.setoid Γ) (sb := Repr.setoid Γ₁) (fun p => p.reindex σ)
    (fun _ _ ⟨hA, ha⟩ => ⟨hA.subst σ.srcWF σ.typed, ha.subst σ.srcWF σ.typed⟩) a

private theorem type_reindex (σ : Raw.Hom Γ₁.as.terms Γ.as.terms) (a : Class Γ) :
    type (reindex σ a) = Ty.Element.reindex σ (type a) := by
  obtain ⟨p⟩ := a
  rfl

private theorem reindex_id (a : Class Γ) (hΓ : ⊢ Γ) : reindex (Raw.Hom.id hΓ) a = a := by
  obtain ⟨p⟩ := a
  change (⟦p.reindex (Raw.Hom.id hΓ)⟧ : Class Γ) = ⟦p⟧
  congr 1
  simp [Repr.reindex]

private theorem reindex_comp (a : Class Γ) (σ : Raw.Hom Γ₁.as.terms Γ.as.terms)
    (τ : Raw.Hom Γ₂.as.terms Γ₁.as.terms) :
    reindex τ (reindex σ a) = reindex (σ.comp τ) a := by
  obtain ⟨p⟩ := a
  change (⟦(p.reindex σ).reindex τ⟧ : Class Γ₂) = ⟦p.reindex (σ.comp τ)⟧
  congr 1
  simp [Repr.reindex, Raw.Hom.comp, subst_subst]

private theorem reindex_eq_of_homEq (a : Class Γ) (W : Raw.HomEq Γ₁.as.terms Γ.as.terms) :
    reindex W.leftHom a = reindex W.rightHom a := by
  obtain ⟨p⟩ := a
  exact Quotient.sound ⟨p.tyWF.subst W.srcWF W.typed, p.valWF.subst W.srcWF W.typed⟩

end Tm.Class

@[implicit_reducible] def Tm.universe : Ctxᵒᵖ ⥤ Type where
  obj Γ := Tm.Class Γ.unop
  map {Γ Δ} σ := ↾Quot.lift (fun σ : Δ.unop.as ⟶ Γ.unop.as => Tm.Class.reindex σ)
    (fun σ τ h => funext fun a => Tm.Class.reindex_eq_of_homEq a
      ⟨Δ.unop.as.wf, σ.subst, τ.subst, (HomRel.compClosure_iff_self RawCtx.homRel σ τ).mp h⟩) σ.unop
  map_id Γ := ConcreteCategory.hom_ext _ _ (Tm.Class.reindex_id · Γ.unop.as.wf)
  map_comp := by
    rintro _ _ _ ⟨σ⟩ ⟨τ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    obtain ⟨τ, rfl⟩ := RawCtx.toCtx.map_surjective τ
    exact ConcreteCategory.hom_ext _ _ fun a => (Tm.Class.reindex_comp a σ τ).symm

def Tm.typing : Tm.universe ⟶ Ty.universe where
  app _ := ↾Tm.type
  naturality := by
    rintro ⟨Γ⟩ ⟨Δ⟩ ⟨σ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    exact ConcreteCategory.hom_ext _ _ (Tm.Class.type_reindex σ)

abbrev Tm (Γ : Ctx) (A : Ty Γ) := {a : yoneda.obj Γ ⟶ Tm.universe // a ≫ Tm.typing = A}

namespace Tm

private theorem hext {A B : Ty Γ} {a : Tm Γ A} {b : Tm Γ B} (h : a.val = b.val) : a ≍ b := by
  obtain ⟨a, rfl⟩ := a
  obtain ⟨b, rfl⟩ := b
  obtain rfl := h
  rfl

@[expose, implicit_reducible] def presheaf : Ctxᵒᵖ ⥤ Type := Presheaf.typedTerms typing

def ofTyping {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) :
    Tm ⟨Γ, hΓ⟩ (Ty.ofTyping hΓ hA) :=
  ⟨yonedaEquiv.symm (⟦Repr.ofTyping hΓ hA ha⟧ : Class ⟨Γ, hΓ⟩),
    yonedaEquiv_symm_naturality_right _ _ _⟩

def pairOfTyping {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (ha : Γ ⊢ a : A) :
    Σ A : Ty ⟨Γ, hΓ⟩, Tm ⟨Γ, hΓ⟩ A :=
  ⟨Ty.ofTyping hΓ hA, ofTyping hΓ hA ha⟩

theorem pairOfTyping_eq_iff {Γ : List Term} {hΓ : ⊢ Γ}
    {hA : Γ ⊢ A : .sort u} {ha : Γ ⊢ a : A}
    {hB : Γ ⊢ B : .sort v} {hb : Γ ⊢ b : B} :
    pairOfTyping hΓ hA ha = pairOfTyping hΓ hB hb ↔
      Γ ⊢ A ≡ B type ∧ Γ ⊢ a ≡ b : A := by
  constructor
  · intro h
    exact Quotient.exact (yonedaEquiv.symm.injective (congrArg (fun a => a.2.val) h))
  · intro h
    exact Sigma.ext ((Ty.ofTyping_eq_iff hΓ hA hB).mpr h.1) (hext (congrArg yonedaEquiv.symm (Quotient.sound h)))

theorem pairOfTyping_eq {Γ : List Term} {hΓ : ⊢ Γ}
    {hA : Γ ⊢ A : .sort u} {ha : Γ ⊢ a : A}
    {hB : Γ ⊢ B : .sort v} {hb : Γ ⊢ b : B}
    (hAB : Γ ⊢ A ≡ B type) (hab : Γ ⊢ a ≡ b : A) :
    pairOfTyping hΓ hA ha = pairOfTyping hΓ hB hb :=
  pairOfTyping_eq_iff.mpr ⟨hAB, hab⟩

@[simp] theorem map_ofTyping (hA : Γ.as.terms ⊢ A : .sort u)
    (ha : Γ.as.terms ⊢ a : A) (σ : Raw.Hom Δ.as.terms Γ.as.terms) :
    presheaf.map (RawCtx.toCtx.map σ).op (pairOfTyping Γ.as.wf hA ha) =
      pairOfTyping Δ.as.wf (hA.subst σ.srcWF σ.typed) (ha.subst σ.srcWF σ.typed) := by
  apply Sigma.ext (Ty.reindex_ofRepr σ ⟨A, hA.type⟩)
  apply hext
  exact yonedaEquiv_symm_naturality_left _ _ _

theorem pairOfTyping_congr {Γ : List Term} (hΓ : ⊢ Γ)
    (hA : Γ ⊢ A ≡ A' : .sort u) (ha : Γ ⊢ a ≡ a' : A) :
    pairOfTyping hΓ hA.hasType.1 ha.hasType.1 =
      pairOfTyping hΓ hA.hasType.2 (hA.defeqDF ha.hasType.2) :=
  pairOfTyping_eq hA.type ha

@[expose] def rawBinderVar {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) : Σ B : Ty (Ctx.extension ⟨Γ, hΓ⟩ hA), Tm (Ctx.extension ⟨Γ, hΓ⟩ hA) B :=
  pairOfTyping (.cons hΓ hA)
    hA.weak
    (.bvar .zero hA.weak)

theorem rawBinderVar_congr {Γ : List Term} {A : Term} {u v : Bool}
    (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u) (hA' : Γ ⊢ A : .sort v) :
    rawBinderVar hΓ hA = rawBinderVar hΓ hA' := by rfl

theorem inst_rawBinderVar {Γ : List Term} (hΓ : ⊢ Γ) (hA : Γ ⊢ A : .sort u)
    (he : Γ ⊢ e : A) :
    presheaf.map (RawCtx.toCtx.map (Raw.Hom.one hΓ he)).op (rawBinderVar hΓ hA) = pairOfTyping hΓ hA he := by
  unfold rawBinderVar
  erw [map_ofTyping]
  apply pairOfTyping_eq ⟨u, ?_⟩ ?_
  · change Γ ⊢ A⟨↑⟩[e/] ≡ A : .sort u
    rw [lift_inst]
    exact hA
  · change Γ ⊢ (Term.bvar 0)[e/] ≡ e : A⟨↑⟩[e/]
    rw [lift_inst]
    exact he

end Tm

namespace Ctx

open Limits

@[expose] def projectionRaw (Γ₁ : Ctx) (hA : Γ₁.as.terms ⊢ A : .sort u) :
    ((extension Γ₁ hA).as ⟶ Γ₁.as) where
  srcWF := (extension Γ₁ hA).as.wf
  subst := (↑ >> Term.bvar)
  typed := (Raw.SubstEq.id Γ₁.as.wf).skip

@[expose] def rawProjection (Γ₁ : Ctx) (hA : Γ₁.as.terms ⊢ A : .sort u) :
    extension Γ₁ hA ⟶ Γ₁ :=
  RawCtx.toCtx.map (projectionRaw Γ₁ hA)

@[simp]
theorem projectionRaw_comp_subst {Γ₁ : Ctx} (Γ₂ : Ctx)
    (hA : Γ₂.as.terms ⊢ A : .sort u) (σ₁ : Γ₁.as ⟶ (extension Γ₂ hA).as) :
    ((projectionRaw Γ₂ hA).comp σ₁).subst = (↑ >> σ₁.subst) := by
  funext i
  rfl

@[simp]
theorem cons_projection {Γ₁ : Ctx} (Γ₂ : Ctx) (hA : Γ₂.as.terms ⊢ A : .sort u)
    (σ₁ : Γ₁.as ⟶ Γ₂.as) (e : Term)
    (he : Γ₁.as.terms ⊢ e : A[σ₁.subst]) :
    RawCtx.toCtx.map (σ₁.cons hA e he) ≫
        rawProjection Γ₂ hA =
      RawCtx.toCtx.map σ₁ := by
  change RawCtx.toCtx.map (σ₁.cons hA e he) ≫
      RawCtx.toCtx.map (projectionRaw Γ₂ hA) = RawCtx.toCtx.map σ₁
  rw [← RawCtx.toCtx.map_comp]
  congr 1

private theorem extension_hom_ext
    {Γ₁ Γ₂ : Ctx}
    {hA : Γ₂.as.terms ⊢ A : .sort u} {σ₁ σ₂ : Γ₁ ⟶ extension Γ₂ hA}
    (hover : σ₁ ≫ rawProjection Γ₂ hA = σ₂ ≫ rawProjection Γ₂ hA)
    (hgeneric : Tm.presheaf.map σ₁.op
    (Tm.rawBinderVar Γ₂.as.wf hA) =
    Tm.presheaf.map σ₂.op
    (Tm.rawBinderVar Γ₂.as.wf hA)) : σ₁ = σ₂ := by
  obtain ⟨σ₁, rfl⟩ := RawCtx.toCtx.map_surjective σ₁
  obtain ⟨σ₂, rfl⟩ := RawCtx.toCtx.map_surjective σ₂
  apply (RawCtx.toCtx_map_eq_iff _ _).mpr
  have htail : Γ₁.as.terms ⊢ (↑ >> σ₁.subst) ≡ (↑ >> σ₂.subst) ⊣ Γ₂.as.terms := by
    have htail' := (RawCtx.toCtx_map_eq_iff ((projectionRaw Γ₂ hA).comp σ₁)
      ((projectionRaw Γ₂ hA).comp σ₂)).mp hover
    rwa [projectionRaw_comp_subst, projectionRaw_comp_subst] at htail'
  unfold Tm.rawBinderVar at hgeneric
  erw [Tm.map_ofTyping, Tm.map_ofTyping] at hgeneric
  refine .cons htail hA ?_
  simpa! [renSubst_Term] using (Tm.pairOfTyping_eq_iff.mp hgeneric).2

theorem rawExtensionIsRepresented (hA : Γ.as.terms ⊢ A : .sort u) :
    IsPullback (Tm.rawBinderVar Γ.as.wf hA).2.val (yoneda.map (rawProjection Γ hA))
      Tm.typing (Ty.ofTyping Γ.as.wf hA) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨Δ⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro σ
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    apply (Ty.Element.ofRepr_eq_iff _ _).mpr
    change Δ ⊢ A⟨↑⟩[σ.subst] ≡ (A[((projectionRaw Γ hA).comp σ).subst]) type
    rw [renSubst_Term, projectionRaw_comp_subst]
    simpa only [projectionRaw_comp_subst] using
      hA.type.subst σ.srcWF ((projectionRaw Γ hA).comp σ).typed
  · intro σ τ ⟨hgeneric, hover⟩
    apply extension_hom_ext hover
    apply (Equiv.sigmaFiberEquiv (fun a : yoneda.obj Δ ⟶ Tm.universe => a ≫ Tm.typing)).injective
    apply yonedaEquiv.injective
    change yonedaEquiv (yoneda.map σ ≫ (Tm.rawBinderVar Γ.as.wf hA).2.val) =
      yonedaEquiv (yoneda.map τ ≫ (Tm.rawBinderVar Γ.as.wf hA).2.val)
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hgeneric
  · intro a σ h
    obtain ⟨a⟩ := a
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    have hty : Δ ⊢ a.ty ≡ (A[σ.subst]) type := (Ty.Element.ofRepr_eq_iff _ _).mp h
    have ha := hty.choose_spec.defeqDF a.valWF
    refine ⟨RawCtx.toCtx.map (σ.cons hA a.val ha), ?_, cons_projection Γ hA σ a.val ha⟩
    apply Quotient.sound
    change _ ∧ _
    simpa [Tm.Repr.reindex, Tm.Repr.ofTyping, lift_subst_cons] using And.intro hty.symm ha


def projection (Γ : Ctx) (A : Ty Γ) : Γ.extend A ⟶ Γ :=
  Γ.rawProjection (Ty.repr A).wf.choose_spec

def generic (A : Ty Γ) : Tm (Γ.extend A) (Ty.presheaf.map (Γ.projection A).op A) := by
  refine ⟨(Tm.rawBinderVar Γ.as.wf (Ty.repr A).wf.choose_spec).2.val, ?_⟩
  have h := (rawExtensionIsRepresented (Ty.repr A).wf.choose_spec).w
  have hA : Ty.ofTyping Γ.as.wf (Ty.repr A).wf.choose_spec = A := Ty.ofRepr_repr A
  change (Tm.rawBinderVar Γ.as.wf (Ty.repr A).wf.choose_spec).2.val ≫ Tm.typing =
    yoneda.map (Γ.rawProjection (Ty.repr A).wf.choose_spec) ≫ A
  rw [hA] at h
  exact h

theorem extensionIsRepresented (A : Ty Γ) :
    IsPullback (generic A).val (yoneda.map (Γ.projection A)) Tm.typing A := by
  have h := rawExtensionIsRepresented (Ty.repr A).wf.choose_spec
  have hA : Ty.ofTyping Γ.as.wf (Ty.repr A).wf.choose_spec = A := Ty.ofRepr_repr A
  change IsPullback (Tm.rawBinderVar Γ.as.wf (Ty.repr A).wf.choose_spec).2.val
    (yoneda.map (Γ.rawProjection (Ty.repr A).wf.choose_spec)) Tm.typing A
  rw [hA] at h
  exact h

@[expose, implicit_reducible] def comprehension : Presheaf.Comprehension Tm.typing where
  obj {Γ} A := Γ.extend A
  projection := Ctx.projection _
  generic A := (Ctx.generic A).val
  isPullback := extensionIsRepresented

abbrev pair (A : Ty Γ) (σ : Δ ⟶ Γ) (a : Tm Δ (Ty.presheaf.map σ.op A)) : Δ ⟶ Γ.extend A :=
  comprehension.pair A σ a.val a.property

abbrev homEquiv (A : Ty Γ) : (Δ ⟶ Γ.extend A) ≃ Σ σ : Δ ⟶ Γ, Tm Δ (Ty.presheaf.map σ.op A) :=
  comprehension.homEquiv A

abbrev lift (σ : Δ ⟶ Γ) (A : Ty Γ) : Δ.extend (Ty.presheaf.map σ.op A) ⟶ Γ.extend A :=
  comprehension.lift σ A

@[simp] private theorem lift_toCtx (σ : Raw.Hom Δ.as.terms Γ.as.terms) (A : Ty Γ) :
    lift (RawCtx.toCtx.map σ) A = RawCtx.toCtx.map (liftRaw σ A) := by
  apply comprehension.hom_ext
  · erw [Presheaf.Comprehension.lift_generic]
    symm
    have ht : Tm.presheaf.map (RawCtx.toCtx.map (liftRaw σ A)).op
        (Tm.rawBinderVar Γ.as.wf (Ty.repr A).wf.choose_spec) =
          Tm.rawBinderVar Δ.as.wf (Ty.repr (Ty.reindex σ A)).wf.choose_spec := by
      unfold Tm.rawBinderVar
      erw [Tm.map_ofTyping]
      apply Tm.pairOfTyping_eq
      · have h := (Ty.repr_reindex A σ).choose_spec.weak
          (B := (Ty.repr (Ty.reindex σ A)).term)
        simpa! [liftRaw, lift_subst_lift, Ctx.extend, Ctx.extension] using h.type
      · exact (IsDefEq.bvar .zero (Ty.repr A).wf.choose_spec.weak).subst
          (liftRaw σ A).srcWF (liftRaw σ A).typed
    exact congrArg (fun a => a.2.val) ht
  · erw [Presheaf.Comprehension.lift_projection]
    symm
    change RawCtx.toCtx.map (liftRaw σ A) ≫
        RawCtx.toCtx.map (projectionRaw Γ (Ty.repr A).wf.choose_spec) =
      RawCtx.toCtx.map (projectionRaw Δ (Ty.repr (Ty.reindex σ A)).wf.choose_spec) ≫ RawCtx.toCtx.map σ
    erw [← RawCtx.toCtx.map_comp, ← RawCtx.toCtx.map_comp]
    congr 1
    apply Raw.Hom.ext
    funext i
    change (σ.subst i)⟨↑⟩ = (σ.subst i)[↑ >> Term.bvar]
    exact rinstInst'_Term _ _

abbrev ContextSection (A : Ty Γ) (σ : Δ ⟶ Γ) (label : Σ B : Ty Δ, Tm Δ B) :=
  Presheaf.Section (q := ⟨_, generic A⟩) (comprehension.isPullback A) σ label

@[reassoc (attr := simp)] theorem pair_projection (A : Ty Γ) (σ : Δ ⟶ Γ)
    (a : Tm Δ (Ty.presheaf.map σ.op A)) : pair A σ a ≫ Γ.projection A = σ :=
  comprehension.pair_projection A σ a.val a.property

@[reassoc (attr := simp)] theorem pair_generic (A : Ty Γ) (σ : Δ ⟶ Γ)
    (a : Tm Δ (Ty.presheaf.map σ.op A)) : yoneda.map (pair A σ a) ≫ (generic A).val = a.val :=
  comprehension.pair_generic A σ a.val a.property

@[reassoc (attr := simp)] theorem lift_projection (σ : Δ ⟶ Γ) (A : Ty Γ) :
    lift σ A ≫ Γ.projection A = Δ.projection (Ty.presheaf.map σ.op A) ≫ σ :=
  comprehension.lift_projection σ A

@[reassoc (attr := simp)] theorem lift_generic (σ : Δ ⟶ Γ) (A : Ty Γ) :
    yoneda.map (lift σ A) ≫ (generic A).val = (generic (Ty.presheaf.map σ.op A)).val :=
  comprehension.lift_generic σ A

@[simp] theorem lift_id (A : Ty Γ) :
    lift (𝟙 Γ) A = eqToHom (congrArg Γ.extend (Ty.presheaf.map_id_apply (op Γ) A)) :=
  comprehension.lift_id A

theorem lift_comp (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : Ty Γ) :
    lift (τ ≫ σ) A = eqToHom (congrArg Θ.extend (Ty.presheaf.map_comp_apply σ.op τ.op A)) ≫
      lift τ (Ty.presheaf.map σ.op A) ≫ lift σ A :=
  comprehension.lift_comp σ τ A

theorem lift_isPullback (σ : Δ ⟶ Γ) (A : Ty Γ) :
    IsPullback (lift σ A) (Δ.projection (Ty.presheaf.map σ.op A)) (Γ.projection A) σ :=
  comprehension.lift_isPullback σ A

abbrev ContextSection.equiv (A : Ty Γ) (σ : Δ ⟶ Γ) (label : Σ B : Ty Δ, Tm Δ B) :
    ContextSection A σ label ≃ (label.1 = Ty.presheaf.map σ.op A) :=
  Presheaf.Section.equiv (q := ⟨_, generic A⟩) (extensionIsRepresented A) σ label

abbrev ContextSection.ofTerm (A : Ty Γ) (σ : Δ ⟶ Γ) (a : Tm Δ (Ty.presheaf.map σ.op A)) :
    ContextSection A σ ⟨_, a⟩ := (ContextSection.equiv A σ ⟨_, a⟩).symm rfl

end Ctx

theorem Tm.typing_representable : yoneda.relativelyRepresentable Tm.typing :=
  fun {Γ} A => ⟨Γ.extend A, Γ.projection A, (Ctx.generic A).val, Ctx.extensionIsRepresented A⟩

@[expose] def Ctx.rawDisplay (hA : Γ.as.terms ⊢ A : .sort u) :
    Presheaf.Display Tm.typing Γ (Γ.extension hA) where
  type := Ty.ofTyping Γ.as.wf hA
  projection := Γ.rawProjection hA
  generic := Tm.rawBinderVar Γ.as.wf hA
  isPullback := Ctx.rawExtensionIsRepresented hA

theorem Ctx.rawDisplay_congr (hA : Γ.as.terms ⊢ A : .sort u) (hA' : Γ.as.terms ⊢ A : .sort v) :
    rawDisplay hA = rawDisplay hA' := by rfl

@[expose] def Ctx.display (A : Ty Γ) : Presheaf.Display Tm.typing Γ (Γ.extend A) where
  type := A
  projection := Γ.projection A
  generic := ⟨_, Ctx.generic A⟩
  isPullback := Ctx.extensionIsRepresented A

abbrev Raw.ContextSection (hA : Γ.as.terms ⊢ A : .sort u) (σ : Δ ⟶ Γ)
    (label : Σ B : Ty Δ, Tm Δ B) :=
  Presheaf.Section (q := Tm.rawBinderVar Γ.as.wf hA) (Ctx.rawExtensionIsRepresented hA) σ label

def Raw.ContextSection.intrinsicEquiv (hA : Γ.as.terms ⊢ A : .sort u) (σ : Δ ⟶ Γ)
    (label : Σ B : Ty Δ, Tm Δ B) :
    Raw.ContextSection hA σ label ≃ Ctx.ContextSection (Ty.ofTyping Γ.as.wf hA) σ label :=
  (Presheaf.Section.equiv (q := Tm.rawBinderVar Γ.as.wf hA) (Ctx.rawExtensionIsRepresented hA) σ label).trans
    (Ctx.ContextSection.equiv (Ty.ofTyping Γ.as.wf hA) σ label).symm

namespace Ty

@[expose, implicit_reducible] def pairPresheaf : Ctxᵒᵖ ⥤ Type :=
  Ctx.comprehension.polynomial.obj presheaf

@[simp] theorem pairPresheaf_map_ofTyping (hA : Γ.as.terms ⊢ A : .sort u)
    (hB : A :: Γ.as.terms ⊢ B : .sort v) (σ : Raw.Hom Δ.as.terms Γ.as.terms) :
    pairPresheaf.map (RawCtx.toCtx.map σ).op (pairOfTyping Γ.as.wf hA hB) =
      pairOfTyping Δ.as.wf (hA.subst σ.srcWF σ.typed)
        (A := A[σ.subst]) (B := B[⇑σ.subst]) (v := v)
        (by simpa! using
          hB.subst (.cons σ.srcWF (hA.subst σ.srcWF σ.typed)) (σ.lift hA).typed) := by
  change (⟨_, presheaf.map (Ctx.lift (RawCtx.toCtx.map σ) (pairOfTyping Γ.as.wf hA hB).1).op
    (pairOfTyping Γ.as.wf hA hB).2⟩ : Σ A : Ty Δ, Ty (Δ.extend A)) = _
  rw [Ctx.lift_toCtx]
  change reindexPair σ (pairOfTyping Γ.as.wf hA hB) = _
  unfold reindexPair pairOfTyping
  rw [map_extensionIso]
  apply Sigma.ext (reindex_ofRepr σ ⟨A, hA.type⟩)
  dsimp only
  erw [map_extensionIso]
  unfold ofTyping
  conv_lhs => arg 2; erw [reindex_ofRepr]
  conv_lhs => erw [reindex_ofRepr]
  conv_rhs => erw [reindex_ofRepr]
  apply heq_of_ctx_eq (congrArg Δ.extend (reindex_ofRepr σ ⟨A, hA.type⟩))
  simpa [Raw.Hom.convert, Ctx.liftRaw, ofTyping] using
    (IsDefEq.convCtxHead Γ.as.wf (repr_eq ⟨A, hA.type⟩).choose_spec hB).type.subst
      (Ctx.liftRaw σ (ofTyping Γ.as.wf hA)).srcWF (Ctx.liftRaw σ (ofTyping Γ.as.wf hA)).typed

end Ty

end DomainSemantics
