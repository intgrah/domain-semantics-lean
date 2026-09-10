/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Soundness.Admissible
import DomainSemantics.Meta.Judgement

@[expose] public section

namespace DomainSemantics

open CategoryTheory

namespace Ctx

structure VariableMap (Γ₁ Γ : Ctx) where
  index : ℕ → ℕ
  typed : Γ₁.as.terms ⊢ (fun i ↦ .bvar (index i)) ≡ (fun i ↦ .bvar (index i)) ⊣ Γ.as.terms

namespace VariableMap

variable {Γ Γ₁ Γ₂ : Ctx} {A : Term} {u : Bool}

def toRawHom (r : VariableMap Γ₁ Γ) : (Γ₁.as ⟶ Γ.as) where
  srcWF := Γ₁.as.wf
  subst i := .bvar (r.index i)
  typed := r.typed

def hom (r : VariableMap Γ₁ Γ) : Γ₁ ⟶ Γ := RawCtx.toCtx.map r.toRawHom

def tail (hA : Γ.as.terms ⊢ A : .sort u) (r : VariableMap Γ₁ (extension Γ hA)) :
    VariableMap Γ₁ Γ where
  index i := r.index (i + 1)
  typed := ((projectionRaw Γ hA).comp r.toRawHom).typed

@[simp]
theorem tail_hom (hA : Γ.as.terms ⊢ A : .sort u)
    (r : VariableMap Γ₁ (extension Γ hA)) :
    (r.tail hA).hom = r.hom ≫ rawProjection Γ hA :=
  RawCtx.toCtx.map_comp r.toRawHom (projectionRaw Γ hA)

def id (Γ : Ctx) : VariableMap Γ Γ where
  index i := i
  typed := Raw.SubstEq.id Γ.as.wf

@[simp]
theorem id_hom (Γ : Ctx) : (id Γ).hom = 𝟙 Γ := rfl

def projection (Γ : Ctx) (hA : Γ.as.terms ⊢ A : .sort u) :
    VariableMap (extension Γ hA) Γ where
  index := Nat.succ
  typed := (projectionRaw Γ hA).typed

@[simp] theorem projection_hom (Γ : Ctx) (hA : Γ.as.terms ⊢ A : .sort u) :
    (projection Γ hA).hom = Γ.rawProjection hA := rfl

end VariableMap

end Ctx

namespace CoherentShape

variable {Γ Γ₁ Γ₂ : Ctx}

def HasRenaming (Γ : Ctx) (t : Term) : Prop :=
  ∀ {Γ₁ Γ₂ : Ctx} (r : Ctx.VariableMap Γ₁ Γ) (σ : Γ₂ ⟶ Γ₁)
    (ρ : RawValuation Γ₂),
    SourceAdmissible (σ ≫ r.hom) (fun i ↦ ρ (r.index i)) →
      (rawInterpret CodeAssignment.piLimit Γ₁ (t.subst r.toRawHom.subst)).app _ σ.op ρ =
        (rawInterpret CodeAssignment.piLimit Γ t).app _ (σ ≫ r.hom).op
          (fun i ↦ ρ (r.index i))

judgement ContextRen : Ctx → Prop where

  ──────────────────── nil
  ContextRen (RawCtx.toCtx.obj ⟨[], .nil⟩)

  ContextRen Γ
  HasRenaming Γ A
  ──────────────────── cons {Γ : Ctx} {A : Term} {u : Bool} (hA : Γ.as.terms ⊢ A : .sort u)
  ContextRen (Γ.extension hA)

theorem ContextRen.lookup (hΓ : ContextRen Γ) {i : ℕ} {A : Term}
    (hi : Lookup Γ.as.terms i A) (r : Ctx.VariableMap Γ₁ Γ)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hρ : SourceAdmissible (σ ≫ r.hom) (fun j ↦ ρ (r.index j))) :
    (ρ (r.index i)).IsDirected ∧
      CodeAssignment.piLimit.rawExtend
        ((rawInterpret CodeAssignment.piLimit Γ₁ (A.subst r.toRawHom.subst)).app _ σ.op ρ)
        (ρ (r.index i)) = ρ (r.index i) := by
  induction hΓ generalizing Γ₁ i A with
  | nil => cases hi
  | @cons Γ B u hB hΓ hBren ih =>
    have htail : SourceAdmissible (σ ≫ (r.tail hB).hom)
        (fun j ↦ ρ ((r.tail hB).index j)) := by
      rw [Ctx.VariableMap.tail_hom, ← Category.assoc]
      exact hρ.tail hB
    cases hi with
    | zero =>
      have ⟨_, _, hdir, hfixed⟩ := (SourceAdmissible.cons_iff hB _ _).mp hρ
      refine ⟨hdir, ?_⟩
      rw [lift_subst]
      change CodeAssignment.piLimit.rawExtend
        ((rawInterpret CodeAssignment.piLimit Γ₁
          (B.subst (r.tail hB).toRawHom.subst)).app _ σ.op ρ)
        (ρ (r.index 0)) = ρ (r.index 0)
      rw [hBren (r.tail hB) σ ρ htail]
      rw [Ctx.VariableMap.tail_hom, ← Category.assoc]
      exact hfixed
    | succ hi =>
      rw [lift_subst]
      exact ih hi (r.tail hB) σ htail

theorem ContextRen.bvar (hΓ : ContextRen Γ) {i : ℕ} {A : Term}
    (hi : Lookup Γ.as.terms i A) (σ : Γ₂ ⟶ Γ) (ρ : RawValuation Γ₂)
    (hρ : SourceAdmissible σ ρ) :
    ((rawInterpret CodeAssignment.piLimit Γ (.bvar i)).app _ σ.op ρ).IsDirected ∧
      CodeAssignment.piLimit.rawExtend
        ((rawInterpret CodeAssignment.piLimit Γ A).app _ σ.op ρ)
        ((rawInterpret CodeAssignment.piLimit Γ (.bvar i)).app _ σ.op ρ) =
        (rawInterpret CodeAssignment.piLimit Γ (.bvar i)).app _ σ.op ρ := by
  have hρ' : SourceAdmissible (σ ≫ (Ctx.VariableMap.id Γ).hom)
      (fun j ↦ ρ ((Ctx.VariableMap.id Γ).index j)) := by
    rw [Ctx.VariableMap.id_hom, Category.comp_id]
    exact hρ
  have h := hΓ.lookup hi (Ctx.VariableMap.id Γ) σ ρ hρ'
  change (ρ i).IsDirected ∧ CodeAssignment.piLimit.rawExtend
    ((rawInterpret CodeAssignment.piLimit Γ (A.subst Subst.id)).app _ σ.op ρ)
    (ρ i) = ρ i at h
  change (ρ i).IsDirected ∧ CodeAssignment.piLimit.rawExtend
    ((rawInterpret CodeAssignment.piLimit Γ A).app _ σ.op ρ) (ρ i) = ρ i
  simpa using h

end CoherentShape

end DomainSemantics
