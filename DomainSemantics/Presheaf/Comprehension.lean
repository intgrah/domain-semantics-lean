/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Data.Subtype

public noncomputable section

namespace DomainSemantics.Presheaf

open CategoryTheory Opposite Limits

universe u v w

variable {C : Type u} [Category.{v} C] {U E : Cᵒᵖ ⥤ Type v}

@[expose, implicit_reducible] def typedTerms (p : E ⟶ U) : Cᵒᵖ ⥤ Type (max u v) where
  obj Γ := Σ A : yoneda.obj Γ.unop ⟶ U, {a : yoneda.obj Γ.unop ⟶ E // a ≫ p = A}
  map σ := ↾fun ⟨A, a, h⟩ => ⟨yoneda.map σ.unop ≫ A, yoneda.map σ.unop ≫ a, by simp [h]⟩
  map_id Γ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨A, a, rfl⟩
    apply (Equiv.sigmaFiberEquiv (fun a => a ≫ p)).injective
    simp
  map_comp σ τ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨A, a, rfl⟩
    apply (Equiv.sigmaFiberEquiv (fun a => a ≫ p)).injective
    simp

@[expose] def typedTermsEquiv (p : E ⟶ U) (Γ : C) :
    (typedTerms p).obj (op Γ) ≃ (yoneda.obj Γ ⟶ E) :=
  Equiv.sigmaFiberEquiv (fun a : yoneda.obj Γ ⟶ E => a ≫ p)

def typedTermsIso (p : E ⟶ U) : typedTerms p ≅ yoneda.op ⋙ yoneda.obj E :=
  NatIso.ofComponents (fun Γ => (typedTermsEquiv p Γ.unop).toIso) (by intros; rfl)

@[simp] private theorem eqToHom_apply_heq {α β : Type w} (h : α = β) (a : α) :
    (eqToHom h) a ≍ a := by cases h; rfl

structure Section {p : E ⟶ U} {Γ ΓA : C} {A : yoneda.obj Γ ⟶ U} {π : ΓA ⟶ Γ}
    {q : (typedTerms p).obj (op ΓA)} (h : IsPullback q.2.val (yoneda.map π) p A)
    {Δ : C} (σ : Δ ⟶ Γ) (a : (typedTerms p).obj (op Δ)) where
  hom : Δ ⟶ ΓA
  over : hom ≫ π = σ
  generic : (typedTerms p).map hom.op q = a

namespace Section

variable {p : E ⟶ U} {Γ ΓA Δ Θ : C} {A : yoneda.obj Γ ⟶ U} {π : ΓA ⟶ Γ}
  {q : (typedTerms p).obj (op ΓA)} {h : IsPullback q.2.val (yoneda.map π) p A}
  {σ : Δ ⟶ Γ} {a : (typedTerms p).obj (op Δ)}

@[ext] theorem ext {s t : Section h σ a} (heq : s.hom = t.hom) : s = t := by
  cases s; cases t; cases heq; rfl

theorem hom_eq (s t : Section h σ a) : s.hom = t.hom :=
  yoneda.map_injective <| h.hom_ext
    (congrArg (fun a => a.2.val) (s.generic.trans t.generic.symm))
    (by simpa using congrArg yoneda.map (s.over.trans t.over.symm))

instance : Subsingleton (Section h σ a) := ⟨fun s t => ext (hom_eq s t)⟩

@[expose] def pullback (s : Section h σ a) (τ : Θ ⟶ Δ) :
    Section h (τ ≫ σ) ((typedTerms p).map τ.op a) where
  hom := τ ≫ s.hom
  over := by simp [s.over]
  generic := by simp [s.generic]

@[expose] def pullbackId {a : (typedTerms p).obj (op Γ)} (s : Section h (𝟙 Γ) a) (σ : Δ ⟶ Γ) :
    Section h σ ((typedTerms p).map σ.op a) where
  hom := σ ≫ s.hom
  over := by simp [s.over]
  generic := by simp [s.generic]

@[expose] def ofHom (h : IsPullback q.2.val (yoneda.map π) p A) (σ : Δ ⟶ ΓA) :
    Section h (σ ≫ π) ((typedTerms p).map σ.op q) := ⟨σ, rfl, rfl⟩

def ofTerm (h : IsPullback q.2.val (yoneda.map π) p A) (σ : Δ ⟶ Γ)
    (a : (typedTerms p).obj (op Δ)) (ha : a.1 = yoneda.map σ ≫ A) : Section h σ a where
  hom := yoneda.preimage (h.lift a.2.val (yoneda.map σ) (a.2.property.trans ha))
  over := yoneda.map_injective (by simp)
  generic := by
    apply (typedTermsEquiv p Δ).injective
    simp [typedTermsEquiv, typedTerms]

def equiv (h : IsPullback q.2.val (yoneda.map π) p A) (σ : Δ ⟶ Γ)
    (a : (typedTerms p).obj (op Δ)) : Section h σ a ≃ (a.1 = yoneda.map σ ≫ A) where
  toFun s := by
    have hq := congrArg (fun a => a.2.val ≫ p) s.generic
    change (yoneda.map s.hom ≫ q.2.val) ≫ p = a.2.val ≫ p at hq
    rw [a.2.property] at hq
    rw [Category.assoc, h.w, ← Category.assoc, ← Functor.map_comp, s.over] at hq
    exact hq.symm
  invFun := ofTerm h σ a
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

@[expose] def map {Γ' ΓA' : C} {A' : yoneda.obj Γ' ⟶ U} {π' : ΓA' ⟶ Γ'}
    {q' : (typedTerms p).obj (op ΓA')} {h' : IsPullback q'.2.val (yoneda.map π') p A'}
    (s : Section h σ a) (f : ΓA ⟶ ΓA') {σ' : Δ ⟶ Γ'}
    (hover : s.hom ≫ f ≫ π' = σ') (hq : (typedTerms p).map f.op q' = q) :
    Section h' σ' a where
  hom := s.hom ≫ f
  over := by simpa using hover
  generic := by simp [hq, s.generic]

@[expose] def lift {Γ' ΓA' : C} {A' : yoneda.obj Γ' ⟶ U} {π' : ΓA' ⟶ Γ'}
    {q' : (typedTerms p).obj (op ΓA')} {h' : IsPullback q'.2.val (yoneda.map π') p A'}
    {f : ΓA' ⟶ ΓA} {g : Γ' ⟶ Γ} (hf : IsPullback f π' π g)
    (hq : (typedTerms p).map f.op q = q') {τ : Δ ⟶ Γ'} (s : Section h (τ ≫ g) a) :
    Section h' τ a where
  hom := hf.lift s.hom τ s.over
  over := hf.lift_snd _ _ _
  generic := by
    rw [← hq, ← Functor.map_comp_apply, ← op_comp, hf.lift_fst]
    exact s.generic

@[expose] def graph {X : Cᵒᵖ ⥤ Type v} (h : IsPullback q.2.val (yoneda.map π) p A)
    (f : yoneda.obj ΓA ⟶ X) (σ : Δ ⟶ Γ) (a : (typedTerms p).obj (op Δ)) (b : X.obj (op Δ)) : Prop :=
  ∃ s : Section h σ a, f.app _ s.hom = b

theorem graph_functional {X : Cᵒᵖ ⥤ Type v} {f : yoneda.obj ΓA ⟶ X} {b c : X.obj (op Δ)}
    (hb : graph h f σ a b) (hc : graph h f σ a c) : b = c := by
  obtain ⟨s, rfl⟩ := hb
  obtain ⟨t, rfl⟩ := hc
  rw [s.hom_eq t]

theorem graph_map {X : Cᵒᵖ ⥤ Type v} {f : yoneda.obj ΓA ⟶ X} {b : X.obj (op Δ)}
    (hb : graph h f σ a b) (τ : Θ ⟶ Δ) :
    graph h f (τ ≫ σ) ((typedTerms p).map τ.op a) (X.map τ.op b) := by
  obtain ⟨s, rfl⟩ := hb
  exact ⟨s.pullback τ, f.naturality_apply τ.op s.hom⟩

theorem graph_comp {Γ' ΓA' : C} {A' : yoneda.obj Γ' ⟶ U} {π' : ΓA' ⟶ Γ'}
    {q' : (typedTerms p).obj (op ΓA')} {h' : IsPullback q'.2.val (yoneda.map π') p A'}
    {f : ΓA' ⟶ ΓA} {g : Γ' ⟶ Γ} (hf : IsPullback f π' π g)
    (hq : (typedTerms p).map f.op q = q') {X : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj ΓA ⟶ X) (τ : Δ ⟶ Γ') (a : (typedTerms p).obj (op Δ)) (b : X.obj (op Δ)) :
    graph h k (τ ≫ g) a b ↔ graph h' (yoneda.map f ≫ k) τ a b := by
  constructor
  · intro ⟨s, hs⟩
    exact ⟨s.lift hf hq, by simpa [lift] using hs⟩
  · intro ⟨s, hs⟩
    exact ⟨s.map f (by rw [hf.w, ← Category.assoc, s.over]) hq, hs⟩

end Section

structure Display (p : E ⟶ U) (Γ ΓA : C) where
  type : yoneda.obj Γ ⟶ U
  projection : ΓA ⟶ Γ
  generic : (typedTerms p).obj (op ΓA)
  isPullback : IsPullback generic.2.val (yoneda.map projection) p type

abbrev Display.Section {p : E ⟶ U} {Γ ΓA Δ : C} (D : Display p Γ ΓA)
    (σ : Δ ⟶ Γ) (a : (typedTerms p).obj (op Δ)) := Presheaf.Section D.isPullback σ a

structure Comprehension (p : E ⟶ U) where
  obj {Γ : C} (A : yoneda.obj Γ ⟶ U) : C
  projection {Γ : C} (A : yoneda.obj Γ ⟶ U) : obj A ⟶ Γ
  generic {Γ : C} (A : yoneda.obj Γ ⟶ U) : yoneda.obj (obj A) ⟶ E
  isPullback {Γ : C} (A : yoneda.obj Γ ⟶ U) :
    IsPullback (generic A) (yoneda.map (projection A)) p A

namespace Comprehension

def ofRepresentable {p : E ⟶ U} (h : yoneda.relativelyRepresentable p) : Comprehension p where
  obj := h.pullback
  projection := h.snd
  generic := h.fst
  isPullback := h.isPullback

variable {p : E ⟶ U} (M : Comprehension p) {Γ Δ Θ : C}

@[reassoc (attr := simp)] theorem generic_typing (A : yoneda.obj Γ ⟶ U) :
    M.generic A ≫ p = yoneda.map (M.projection A) ≫ A := (M.isPullback A).w

def pair (A : yoneda.obj Γ ⟶ U) (σ : Δ ⟶ Γ) (a : yoneda.obj Δ ⟶ E)
    (h : a ≫ p = yoneda.map σ ≫ A) : Δ ⟶ M.obj A :=
  yoneda.preimage ((M.isPullback A).lift a (yoneda.map σ) h)

@[reassoc (attr := simp)] theorem pair_projection (A : yoneda.obj Γ ⟶ U) (σ : Δ ⟶ Γ)
    (a : yoneda.obj Δ ⟶ E) (h : a ≫ p = yoneda.map σ ≫ A) :
    M.pair A σ a h ≫ M.projection A = σ := by
  apply yoneda.map_injective
  simp [pair]

@[reassoc (attr := simp)] theorem pair_generic (A : yoneda.obj Γ ⟶ U) (σ : Δ ⟶ Γ)
    (a : yoneda.obj Δ ⟶ E) (h : a ≫ p = yoneda.map σ ≫ A) :
    yoneda.map (M.pair A σ a h) ≫ M.generic A = a := by
  simp [pair]

@[ext] theorem hom_ext {A : yoneda.obj Γ ⟶ U} {σ τ : Δ ⟶ M.obj A}
    (hq : yoneda.map σ ≫ M.generic A = yoneda.map τ ≫ M.generic A)
    (hπ : σ ≫ M.projection A = τ ≫ M.projection A) : σ = τ :=
  yoneda.map_injective <| (M.isPullback A).hom_ext hq (by simpa using congrArg yoneda.map hπ)

def homEquiv (A : yoneda.obj Γ ⟶ U) :
    (Δ ⟶ M.obj A) ≃ Σ σ : Δ ⟶ Γ, {a : yoneda.obj Δ ⟶ E // a ≫ p = yoneda.map σ ≫ A} where
  toFun σ := ⟨σ ≫ M.projection A, yoneda.map σ ≫ M.generic A, by simp⟩
  invFun a := M.pair A a.1 a.2.val a.2.property
  left_inv σ := M.hom_ext (by simp) (by simp)
  right_inv := by
    intro ⟨σ, a, h⟩
    apply Sigma.ext (M.pair_projection A σ a h)
    apply (Subtype.heq_iff_coe_eq (by simp)).mpr
    exact M.pair_generic A σ a h

def lift (σ : Δ ⟶ Γ) (A : yoneda.obj Γ ⟶ U) :
    M.obj (yoneda.map σ ≫ A) ⟶ M.obj A :=
  M.pair A (M.projection (yoneda.map σ ≫ A) ≫ σ) (M.generic (yoneda.map σ ≫ A)) (by simp)

@[reassoc (attr := simp)] theorem lift_projection (σ : Δ ⟶ Γ) (A : yoneda.obj Γ ⟶ U) :
    M.lift σ A ≫ M.projection A = M.projection (yoneda.map σ ≫ A) ≫ σ := by simp [lift]

@[reassoc (attr := simp)] theorem lift_generic (σ : Δ ⟶ Γ) (A : yoneda.obj Γ ⟶ U) :
    yoneda.map (M.lift σ A) ≫ M.generic A = M.generic (yoneda.map σ ≫ A) := by simp [lift]

@[reassoc (attr := simp)] theorem eqToHom_projection {A B : yoneda.obj Γ ⟶ U} (h : A = B) :
    eqToHom (congrArg M.obj h) ≫ M.projection B = M.projection A := by cases h; simp

@[reassoc (attr := simp)] theorem eqToHom_generic {A B : yoneda.obj Γ ⟶ U} (h : A = B) :
    eqToHom (congrArg (fun A => yoneda.obj (M.obj A)) h) ≫ M.generic B = M.generic A := by cases h; simp

@[simp] theorem lift_id (A : yoneda.obj Γ ⟶ U) :
    M.lift (𝟙 Γ) A = eqToHom (by simp : M.obj (yoneda.map (𝟙 Γ) ≫ A) = M.obj A) := by
  apply M.hom_ext <;> simp [lift, eqToHom_map]

theorem lift_comp (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (A : yoneda.obj Γ ⟶ U) :
    M.lift (τ ≫ σ) A =
      eqToHom (by simp : M.obj (yoneda.map (τ ≫ σ) ≫ A) = M.obj (yoneda.map τ ≫ (yoneda.map σ ≫ A))) ≫
        M.lift τ (yoneda.map σ ≫ A) ≫ M.lift σ A := by
  apply M.hom_ext <;> simp [eqToHom_map]

theorem lift_isPullback (σ : Δ ⟶ Γ) (A : yoneda.obj Γ ⟶ U) :
    IsPullback (M.lift σ A) (M.projection (yoneda.map σ ≫ A)) (M.projection A) σ := by
  apply IsPullback.of_map yoneda (M.lift_projection σ A)
  have h := M.isPullback (yoneda.map σ ≫ A)
  rw [← M.lift_generic σ A] at h
  exact h.of_right (by simpa only [Functor.map_comp] using congrArg yoneda.map (M.lift_projection σ A)) (M.isPullback A)

@[expose, implicit_reducible] def polynomial :
    (Cᵒᵖ ⥤ Type (max u v w)) ⥤ (Cᵒᵖ ⥤ Type (max u v w)) where
  obj X := {
    obj Γ := Σ A : yoneda.obj Γ.unop ⟶ U, X.obj (op (M.obj A))
    map σ := ↾fun ⟨A, B⟩ => ⟨yoneda.map σ.unop ≫ A, X.map (M.lift σ.unop A).op B⟩
    map_id Γ := by
      apply ConcreteCategory.hom_ext
      intro ⟨A, B⟩
      simp [eqToHom_map]
    map_comp σ τ := by
      apply ConcreteCategory.hom_ext
      intro ⟨A, B⟩
      simp [M.lift_comp, eqToHom_map]
  }
  map f := {
    app Γ := ↾fun ⟨A, B⟩ => ⟨A, f.app _ B⟩
    naturality := by
      intro Γ Δ σ
      apply ConcreteCategory.hom_ext
      intro ⟨A, B⟩
      dsimp
      apply Sigma.ext (by rfl)
      exact heq_of_eq (f.naturality_apply (M.lift σ.unop A).op B)
  }
  map_id X := by
    apply NatTrans.ext
    funext Γ
    apply ConcreteCategory.hom_ext
    intro ⟨A, B⟩
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext Γ
    apply ConcreteCategory.hom_ext
    intro ⟨A, B⟩
    rfl

end Comprehension

end DomainSemantics.Presheaf
