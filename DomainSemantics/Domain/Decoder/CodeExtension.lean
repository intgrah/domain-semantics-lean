/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.FunctionRetraction
public import Mathlib.Order.Filter.Defs
import DomainSemantics.Presheaf.Approximation

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory MonoidalCategory Presheaf

abbrev CodeAssignment := order ⟶ IdealOperator.presheaf

namespace CodeAssignment

variable {Γ Γ₁ Γ₂ : Ctx}

@[simp] theorem app_reindex (F : CodeAssignment) (a : CoherentShape Γ) (σ : Γ₁ ⟶ Γ) :
    F.app _ (reindex σ a) = IdealOperator.pullback (F.app _ a) σ :=
  ConcreteCategory.congr_hom (F.naturality σ.op) a

noncomputable def eval (F : CodeAssignment) (a : CoherentShape Γ) (X : Domain Γ) : Domain Γ :=
  (F.app _ a).val.app _ (𝟙 Γ).op X

theorem pullback_eval (F : CodeAssignment) (a : CoherentShape Γ)
    (X : Domain Γ) (σ : Γ₁ ⟶ Γ) :
    (F.eval a X).pullback σ = F.eval (reindex σ a) (X.pullback σ) := by
  have h := congrArg (fun P : IdealOperator Γ₁ => P.val.app _ (𝟙 Γ₁).op (X.pullback σ))
    (F.app_reindex a σ)
  change F.eval (reindex σ a) (X.pullback σ) =
    (F.app _ a).val.app _ ((𝟙 Γ₁ ≫ σ).op) (X.pullback σ) at h
  simp at h
  exact (IdealOperator.app_pullback (F.app _ a) (𝟙 Γ).op σ X).symm.trans
    (by simpa using h.symm)

theorem eval_mono_code (F : CodeAssignment) {a b : CoherentShape Γ} (h : a ≤ b)
    (X : Domain Γ) : F.eval a X ≤ F.eval b X :=
  (F.app _).hom.monotone h _ (𝟙 Γ).op X

theorem eval_mono_payload (F : CodeAssignment) (a : CoherentShape Γ)
    {X Y : Domain Γ} (h : X ≤ Y) : F.eval a X ≤ F.eval a Y :=
  ((F.app _ a).val.app _ (𝟙 Γ).op).hom.monotone h

noncomputable def evalStep (F : CodeAssignment) :
    Functor.HomObj (order ⊗ order) (ΩIdeal.presheaf pointedOrder)
      (uliftYoneda.{0}.obj Γ) where
  app _ _ := Preord.ofHom {
    toFun := fun (c, x) => F.eval c (principalIdeal x)
    monotone' := fun _ _ ⟨hc, hx⟩ => fun f a ha =>
      F.eval_mono_payload _ (ΩLower.principal_mono hx) f a
        (F.eval_mono_code hc _ f a ha) }
  naturality σ₁ f := by
    ext ⟨c, x⟩
    change F.eval (reindex σ₁.unop c) (principalIdeal (reindex σ₁.unop x)) =
      (F.eval c (principalIdeal x)).pullback σ₁.unop
    rw [F.pullback_eval, ΩIdeal.presheaf_map_principal]
    rfl

noncomputable abbrev evalStepRaw (F : CodeAssignment) :=
  (F.evalStep (Γ := Γ)).comp (.ofNatTrans (ΩIdeal.toLowerNatTrans pointedOrder))

noncomputable def rawExtend (F : CodeAssignment) (T X : RawValue Γ) : RawValue Γ :=
  ΩLower.bind₂ T X F.evalStepRaw

noncomputable def extend (F : CodeAssignment) (T X : Domain Γ) : Domain Γ :=
  ΩIdeal.bind₂ T X F.evalStep

theorem rawExtend_toLower (F : CodeAssignment) (T X : Domain Γ) :
    F.rawExtend T.val X.val = (F.extend T X).val :=
  rfl

theorem rawExtend_isDirected (F : CodeAssignment) {T X : RawValue Γ}
    (hT : T.IsDirected) (hX : X.IsDirected) : (F.rawExtend T X).IsDirected :=
  (F.extend ⟨T, hT⟩ ⟨X, hX⟩).property

@[simp] theorem mem_rawExtend (F : CodeAssignment) (T X : RawValue Γ)
    (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (F.rawExtend T X).mem σ y ↔
      ∃ c, T.mem σ c ∧ ∃ x, X.mem σ x ∧
        (F.eval c (principalIdeal x)).mem (𝟙 Γ₁) y := by
  rw [rawExtend, ΩLower.mem_bind₂]
  exact ⟨fun ⟨c, x, hc, hx, hy⟩ => ⟨c, hc, x, hx, hy⟩, fun ⟨c, hc, x, hx, hy⟩ => ⟨c, x, hc, hx, hy⟩⟩

@[simp] theorem mem_extend {Γ₁ Γ₂ : Ctx} (F : CodeAssignment)
    (T X : Domain Γ₂) (σ₁ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    (F.extend T X).mem σ₁ y ↔ ∃ a, T.mem σ₁ a ∧
      (F.eval a (X.pullback σ₁)).mem (𝟙 Γ₁) y := by
  rw [← ΩIdeal.val_mem, ← rawExtend_toLower, mem_rawExtend]
  constructor
  · intro ⟨c, hc, x, hx, hy⟩
    refine ⟨c, hc, F.eval_mono_payload c ?_ (𝟙 Γ₁) y hy⟩
    apply ΩLower.principal_le_iff.mpr
    exact (ΩIdeal.presheaf_map_mem_id X σ₁ x).mpr hx
  · intro ⟨c, hc, hy⟩
    have ⟨x, hx, hy⟩ := (F.app _ c).property _ (𝟙 Γ₁).op (X.pullback σ₁) hy
    exact ⟨c, hc, x, (ΩIdeal.presheaf_map_mem_id X σ₁ x).mp hx, hy⟩

theorem rawExtend_mono_left (F : CodeAssignment) {T T' : RawValue Γ}
    (h : T ≤ T') (X : RawValue Γ) : F.rawExtend T X ≤ F.rawExtend T' X :=
  ΩLower.bind₂_mono h (fun _ _ h => h) _

theorem rawExtend_mono_right (F : CodeAssignment) {T : RawValue Γ}
    {X X' : RawValue Γ} (h : X ≤ X') : F.rawExtend T X ≤ F.rawExtend T X' :=
  ΩLower.bind₂_mono (fun _ _ h => h) h _

theorem extend_mono_left (F : CodeAssignment) {T T' : Domain Γ}
    (h : T ≤ T') (X : Domain Γ) : F.extend T X ≤ F.extend T' X :=
  ΩIdeal.bind₂_mono h (fun _ _ h => h) _

theorem extend_mono_right (F : CodeAssignment) {T : Domain Γ}
    {X X' : Domain Γ} (h : X ≤ X') : F.extend T X ≤ F.extend T X' :=
  ΩIdeal.bind₂_mono (fun _ _ h => h) h _

theorem pullback_rawExtend (F : CodeAssignment) (T X : RawValue Γ)
    (σ : Γ₁ ⟶ Γ) :
    (F.rawExtend T X).pullback σ = F.rawExtend (T.pullback σ) (X.pullback σ) := by
  ext Γ₂ σ₁ y
  rw [ΩLower.presheaf_map_mem, mem_rawExtend, mem_rawExtend]
  rfl

theorem pullback_extend (F : CodeAssignment) (T X : Domain Γ)
    (σ : Γ₁ ⟶ Γ) :
    (F.extend T X).pullback σ = F.extend (T.pullback σ) (X.pullback σ) :=
  Subtype.val_injective (F.pullback_rawExtend T.val X.val σ)

noncomputable def rawExtendHom (F : CodeAssignment) :
    ΩLower.presheaf pointedOrder ⊗ ΩLower.presheaf pointedOrder ⟶
      ΩLower.presheaf pointedOrder where
  app _ := Preord.ofHom {
    toFun := fun (T, X) => F.rawExtend T X
    monotone' := fun _ _ ⟨hT, hX⟩ => ΩLower.bind₂_mono hT hX _ }
  naturality _ _ σ := Preord.ext fun (T, X) => (F.pullback_rawExtend T X σ.unop).symm

theorem rawExtend_eventually (F : CodeAssignment) {α : Type*} {l : Filter α}
    {T X : RawValue Γ} {Ts Xs : α → RawValue Γ}
    (hT : ∀ {x}, T.mem (𝟙 Γ) x → ∀ᶠ a in l, (Ts a).mem (𝟙 Γ) x)
    (hX : ∀ {x}, X.mem (𝟙 Γ) x → ∀ᶠ a in l, (Xs a).mem (𝟙 Γ) x)
    {y : CoherentShape Γ} (hy : (F.rawExtend T X).mem (𝟙 Γ) y) :
    ∀ᶠ a in l, (F.rawExtend (Ts a) (Xs a)).mem (𝟙 Γ) y :=
  ΩLower.bind₂_eventually F.evalStepRaw hT hX hy

theorem eval_le_extend (F : CodeAssignment) {T : Domain Γ}
    {a : CoherentShape Γ} (ha : T.mem (𝟙 Γ) a)
    (X : Domain Γ) : F.eval a X ≤ F.extend T X := by
  intro Γ₁ σ y hy
  rw [ΩIdeal.val_mem, mem_extend]
  refine ⟨reindex σ a, ?_, ?_⟩
  · simpa using T.natural (𝟙 Γ) σ a ha
  · have hy' := (ΩIdeal.presheaf_map_mem_id _ σ y).mpr hy
    rw [F.pullback_eval] at hy'
    exact hy'

theorem extend_principal (F : CodeAssignment) (a : CoherentShape Γ)
    (X : Domain Γ) : F.extend (principalIdeal a) X = F.eval a X := by
  ext Γ₁ σ y
  rw [mem_extend]
  constructor
  · intro ⟨c, hc, hy⟩
    have hy := F.eval_mono_code ((principalIdeal_mem a σ c).mp hc) _ (𝟙 Γ₁) y hy
    rw [← F.pullback_eval] at hy
    exact (ΩIdeal.presheaf_map_mem_id _ σ y).mp hy
  · intro hy
    refine ⟨reindex σ a, (principalIdeal_mem a σ _).mpr le_rfl, ?_⟩
    rw [← F.pullback_eval]
    exact (ΩIdeal.presheaf_map_mem_id _ σ y).mpr hy

theorem extend_finitary_left (F : CodeAssignment) (X : Domain Γ) :
    ΩIdeal.IsFinitary fun T => F.extend T X := by
  intro T y hy
  have ⟨a, ha, hy⟩ := (mem_extend _ _ _ _ _).mp hy
  exact ⟨a, ha, (mem_extend _ _ _ _ _).mpr ⟨a, by simp, hy⟩⟩

theorem extend_finitary_right (F : CodeAssignment) (T : Domain Γ) :
    ΩIdeal.IsFinitary (F.extend T) := by
  intro X y hy
  have ⟨a, ha, x, hx, hy⟩ := (mem_rawExtend F T.val X.val (𝟙 Γ) y).mp hy
  exact ⟨x, hx, (mem_rawExtend _ _ _ _ _).mpr ⟨a, ha, x, by simp, hy⟩⟩

noncomputable def decode (F : CodeAssignment) (T : Domain Γ) : IdealOperator Γ where
  val.app _ σ₁ := Preord.ofHom {
    toFun := F.extend (T.pullback σ₁.unop)
    monotone' _ _ h := F.extend_mono_right h }
  val.naturality σ₂ σ₁ := by
    ext X
    change F.extend (T.pullback (σ₁ ≫ σ₂).unop)
      (X.pullback σ₂.unop) =
      (F.extend (T.pullback σ₁.unop) X).pullback σ₂.unop
    rw [unop_comp, ← ΩIdeal.pullback_pullback]
    exact (F.pullback_extend (T.pullback σ₁.unop) X σ₂.unop).symm
  property _ σ := F.extend_finitary_right (T.pullback σ.unop)

def IsIdempotent (F : CodeAssignment) : Prop :=
  ∀ {Γ : Ctx} (a : CoherentShape Γ), IdealOperator.IsIdempotent (F.app _ a)

theorem eval_idempotent {F : CodeAssignment} (hF : F.IsIdempotent)
    (a : CoherentShape Γ) (X : Domain Γ) :
    F.eval a (F.eval a X) = F.eval a X :=
  hF a (𝟙 Γ) X

theorem extend_idempotent {F : CodeAssignment} (hF : F.IsIdempotent)
    (T X : Domain Γ) :
    F.extend T (F.extend T X) = F.extend T X := by
  apply le_antisymm
  · intro Γ₁ σ y
    simp_rw [mem_extend]
    intro ⟨a, ha, hy⟩
    have ⟨x, hx, hy⟩ := (F.app _ a).property _ (𝟙 Γ₁).op ((F.extend T X).pullback σ) hy
    rw [ΩIdeal.presheaf_map_mem_id] at hx
    have ⟨b, hb, hx⟩ := (mem_extend _ _ _ _ _).mp hx
    have ⟨c, hc, hac, hbc⟩ := T.property σ ha hb
    have hxc := F.eval_mono_code hbc (X.pullback σ)
      (𝟙 Γ₁) x hx
    have hyc := F.eval_mono_code hac (principalIdeal x)
      (𝟙 Γ₁) y hy
    have hyc' := F.eval_mono_payload c (ΩLower.principal_le_iff.mpr hxc) (𝟙 Γ₁) y hyc
    rw [F.eval_idempotent hF] at hyc'
    exact ⟨c, hc, hyc'⟩
  · intro Γ₁ σ y
    simp_rw [mem_extend]
    intro ⟨a, ha, hy⟩
    have ha' : (T.pullback σ).mem (𝟙 Γ₁) a :=
      (ΩIdeal.presheaf_map_mem_id T σ a).mpr ha
    have hy' : (F.eval a (F.eval a (X.pullback σ))).mem (𝟙 Γ₁) y := by
      rw [F.eval_idempotent hF]
      exact hy
    refine ⟨a, ha, ?_⟩
    rw [F.pullback_extend]
    exact F.eval_mono_payload a (F.eval_le_extend ha' (X.pullback σ)) (𝟙 Γ₁) y hy'

theorem rawExtend_idempotent (F : CodeAssignment) (hF : F.IsIdempotent)
    {T X : RawValue Γ} (hT : T.IsDirected) (hX : X.IsDirected) :
    F.rawExtend T (F.rawExtend T X) = F.rawExtend T X :=
  congrArg Subtype.val (F.extend_idempotent hF ⟨T, hT⟩ ⟨X, hX⟩)

theorem decode_isIdempotent {F : CodeAssignment} (hF : F.IsIdempotent)
    (T : Domain Γ) : (F.decode T).IsIdempotent :=
  fun σ ↦ F.extend_idempotent hF (T.pullback σ)

theorem decode_mono (F : CodeAssignment) {T T' : Domain Γ}
    (h : T ≤ T') : F.decode T ≤ F.decode T' :=
  fun _ ⟨σ₁⟩ ↦ F.extend_mono_left (ΩIdeal.pullback_mono h σ₁)

@[simp]
theorem pullback_decode (F : CodeAssignment) (T : Domain Γ)
    (σ : Γ₁ ⟶ Γ) : (F.decode T).pullback σ = F.decode (T.pullback σ) := by
  ext Γ₂ ⟨σ₁⟩ X
  exact congrArg (fun T => F.extend T X) (ΩIdeal.pullback_pullback T σ σ₁).symm

theorem decode_principal (F : CodeAssignment) (a : CoherentShape Γ) :
    F.decode (principalIdeal a) = F.app _ a := by
  ext ⟨Γ₁⟩ ⟨σ₁⟩ X
  refine (congrArg (fun T => F.extend T X)
    (ΩIdeal.presheaf_map_principal a σ₁)).trans ?_
  change F.extend (principalIdeal (reindex σ₁ a)) X = _
  rw [F.extend_principal]
  have h := congrArg (fun P : IdealOperator Γ₁ => P.val.app _ (𝟙 Γ₁).op X)
    (F.app_reindex a σ₁)
  change F.eval (reindex σ₁ a) X = (F.app _ a).val.app _ (σ₁.op ≫ (𝟙 Γ₁).op) X at h
  simp at h
  exact h

noncomputable def bottom : CodeAssignment where
  app _ := Preord.ofHom (OrderHom.const _ IdealOperator.bottom)
  naturality _ _ _ := rfl

theorem bottom_le (F : CodeAssignment) : bottom ≤ F :=
  fun _ _ => IdealOperator.bottom_le _

noncomputable instance : OrderBot CodeAssignment where
  bot := bottom
  bot_le := bottom_le

theorem bottom_isIdempotent : bottom.IsIdempotent := by
  intro Γ a Γ₁ σ X
  rfl

end CodeAssignment

end DomainSemantics.CoherentShape
