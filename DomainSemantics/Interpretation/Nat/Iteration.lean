/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Interpretation.Nat.Case
public import DomainSemantics.Domain.Decoder.CodeExtension
import Mathlib.Order.Filter.Basic

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ Γ₂ : Ctx}
variable {C' F' : RawAction Γ} {Z' B' : RawValue Γ}

namespace RawAction

noncomputable def decode (D : CodeAssignment) (C F : RawAction Γ) : RawAction Γ where
  val := (C.val.pair F.val).comp (.ofNatTrans (Functor.whiskerRight D.rawExtendHom (forget Preord)))
  property X σ label :=
    (D.rawExtendHom.app X).hom.monotone.comp
      ((C.property X σ label).prodMk (F.property X σ label))

theorem decode_mono (D : CodeAssignment) {C F : RawAction Γ}
    (hC : C ≤ C') (hF : F ≤ F') : decode D C F ≤ decode D C' F' :=
  fun Γ₁ p I {_} σ₁ y hy => D.rawExtend_mono_right (hF Γ₁ p I) σ₁ y
    (D.rawExtend_mono_left (hC Γ₁ p I) _ σ₁ y hy)

theorem IsFinitary.decode (D : CodeAssignment) {C F : RawAction Γ}
    (hC : C.IsFinitary) (hF : F.IsFinitary) : (decode D C F).IsFinitary :=
  fun σ label => ΩLower.IsFinitary.of_eventually fun I _ =>
    D.rawExtend_eventually (hC.eventually σ label I) (hF.eventually σ label I)

theorem IsIdealValued.decode (D : CodeAssignment) {C F : RawAction Γ}
    (hC : C.IsIdealValued) (hF : F.IsIdealValued) : (decode D C F).IsIdealValued :=
  fun σ label I => D.rawExtend_isDirected (hC σ label I) (hF σ label I)

noncomputable def natCase (R : NatRecLabelRelation Γ) (Z B : RawValue Γ) (F : RawAction Γ) :
    RawAction Γ where
  val.app _ := fun ⟨σ⟩ => ↾fun (_, I) => rawNatCase (R.pullback σ) (Z.pullback σ) (B.pullback σ)
      (presheaf.map σ.op F) I
  val.naturality τ := fun ⟨σ⟩ => by
    refine ConcreteCategory.hom_ext _ _ fun ⟨label, I⟩ => ?_
    change rawNatCase (R.pullback (τ.unop ≫ σ)) (Z.pullback (τ.unop ≫ σ))
      (B.pullback (τ.unop ≫ σ)) (presheaf.map (σ.op ≫ τ) F) (I.pullback τ.unop) =
        (rawNatCase (R.pullback σ) (Z.pullback σ) (B.pullback σ)
          (presheaf.map σ.op F) I).pullback τ.unop
    rw [pullback_rawNatCase, NatRecLabelRelation.pullback_comp,
      ΩLower.pullback_pullback, ΩLower.pullback_pullback, presheaf.map_comp]
    rfl
  property _ _ _ _ _ h := rawNatCase_mono _ (fun _ _ h => h) (fun _ _ h => h) le_rfl h

theorem natCase_mono (R : NatRecLabelRelation Γ)
    {Z B : RawValue Γ} {F : RawAction Γ}
    (hZ : Z ≤ Z') (hB : B ≤ B') (hF : F ≤ F') :
    natCase R Z B F ≤ natCase R Z' B' F' :=
  fun _ ⟨⟨σ⟩, _⟩ _ => rawNatCase_mono _ (ΩLower.pullback_mono hZ σ)
    (ΩLower.pullback_mono hB σ) ((presheaf.map σ.op).hom.monotone hF) (fun _ _ h => h)

theorem natCase_isFinitary (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) : (natCase R Z B F).IsFinitary :=
  fun _ _ => rawNatCase_finitary _ _ _ _

theorem IsIdealValued.natCase (R : NatRecLabelRelation Γ) {Z B : RawValue Γ}
    {F : RawAction Γ} (hZ : Z.IsDirected) (hB : B.IsDirected)
    (hF : F.IsIdealValued) : (natCase R Z B F).IsIdealValued :=
  fun σ _ I => rawNatCase_isDirected _ _ _ _ I (hZ.pullback σ) (hB.pullback σ) (hF.pullback σ)

mutual

inductive NatEvaluates (D : CodeAssignment) (C : RawAction Γ) (R : NatRecLabelRelation Γ)
    (Z B : RawValue Γ) : {Γ₁ : Ctx} → (Γ₁ ⟶ Γ) →
      (Σ A : Ty Γ₁, Tm Γ₁ A) → RawValue Γ₁ → CoherentShape Γ₁ → Prop where
  | eval {Γ₁ σ label X y} (c x : CoherentShape Γ₁)
      (hc : (C.app _ (σ.op, label) X).mem (𝟙 Γ₁) c)
      (hx : NatCaseEvaluates D C R Z B σ X x)
      (hy : (D.eval c (principalIdeal x)).mem (𝟙 Γ₁) y) : NatEvaluates D C R Z B σ label X y

inductive NatCaseEvaluates (D : CodeAssignment) (C : RawAction Γ) (R : NatRecLabelRelation Γ)
    (Z B : RawValue Γ) : {Γ₁ : Ctx} → (Γ₁ ⟶ Γ) → RawValue Γ₁ → CoherentShape Γ₁ → Prop where
  | bottom {Γ₁ σ X} {x : CoherentShape Γ₁} (hx : x ≤ ⊥) : NatCaseEvaluates D C R Z B σ X x
  | zero {Γ₁ σ X x} (hz : X.mem (𝟙 Γ₁) zeroAtom) (hx : Z.mem σ x) :
      NatCaseEvaluates D C R Z B σ X x
  | succ {Γ₁ σ X p pre res u r x}
      (hp : X.mem (𝟙 Γ₁) (succMap pre p)) (hr : R.holds σ pre res)
      (hu : (rawApplication (B.pullback σ) {pre} (principalIdeal p).val).mem (𝟙 Γ₁) u)
      (recursive : NatEvaluates D C R Z B σ pre (principalIdeal p).val r)
      (hx : (application (principalIdeal u) res (principalIdeal r)).mem (𝟙 Γ₁) x) :
      NatCaseEvaluates D C R Z B σ X x

end

namespace NatEvaluates

variable {D : CodeAssignment} {C : RawAction Γ} {R : NatRecLabelRelation Γ}
  {Z B : RawValue Γ} {σ : Γ₁ ⟶ Γ} {label : Σ A : Ty Γ₁, Tm Γ₁ A} {X : RawValue Γ₁}
  {y z : CoherentShape Γ₁}

theorem bottom : NatEvaluates D C R Z B σ label X ⊥ :=
  ⟨_, _, (C.app _ _ X).bottom _, .bottom le_rfl, (D.eval _ _).bottom _⟩

theorem lower (h : NatEvaluates D C R Z B σ label X y) (hz : z ≤ y) :
    NatEvaluates D C R Z B σ label X z :=
  have ⟨c, x, hc, hx, hy⟩ := h
  ⟨c, x, hc, hx, (D.eval _ _).lower _ hz hy⟩

theorem mono (h : NatEvaluates D C R Z B σ label X y) {X' : RawValue Γ₁} (hX : X ≤ X') :
    NatEvaluates D C R Z B σ label X' y :=
  have ⟨c, x, hc, hx, hy⟩ := h
  ⟨c, x, (C.app _ _).hom.monotone hX _ _ hc, match hx with
    | .bottom hx => .bottom hx
    | .zero hz hx => .zero (hX _ _ hz) hx
    | .succ hp hr hu hrec hx => .succ (hX _ _ hp) hr hu hrec hx, hy⟩

end NatEvaluates

variable {D : CodeAssignment} {C : RawAction Γ} {R : NatRecLabelRelation Γ} {Z B : RawValue Γ}

mutual

theorem NatEvaluates.reindex {Γ₁ Γ₂ : Ctx} {σ : Γ₁ ⟶ Γ} {label X y}
    (h : NatEvaluates D C R Z B σ label X y) (τ : Γ₂ ⟶ Γ₁) :
    NatEvaluates D C R Z B (τ ≫ σ) (Tm.presheaf.map τ.op label) (X.pullback τ)
      (CoherentShape.reindex τ y) :=
  have ⟨c, x, hc, hx, hy⟩ := h
  ⟨CoherentShape.reindex τ c, CoherentShape.reindex τ x, by
    rw [CategoryTheory.op_comp, app_pullback, ΩLower.presheaf_map_mem_id]
    simpa using (C.app _ _ X).natural (𝟙 _) τ _ hc,
    NatCaseEvaluates.reindex hx τ, by
      have h : (D.eval c (principalIdeal x)).mem τ (CoherentShape.reindex τ y) := by
        simpa using (D.eval c (principalIdeal x)).natural (𝟙 Γ₁) τ y hy
      simpa only [D.pullback_eval, ΩIdeal.presheaf_map_principal, pointedOrder_map, Quiver.Hom.unop_op] using
        (ΩIdeal.presheaf_map_mem_id _ τ _).mpr h⟩

theorem NatCaseEvaluates.reindex {Γ₁ Γ₂ : Ctx} {σ : Γ₁ ⟶ Γ} {X x}
    (h : NatCaseEvaluates D C R Z B σ X x) (τ : Γ₂ ⟶ Γ₁) :
    NatCaseEvaluates D C R Z B (τ ≫ σ) (X.pullback τ) (CoherentShape.reindex τ x) :=
  match h with
  | .bottom hx => .bottom (LE.reindex τ hx)
  | .zero hz hx => .zero (by
      change X.mem _ (CoherentShape.reindex τ zeroAtom)
      simpa using X.natural (𝟙 _) τ zeroAtom hz) (Z.natural σ τ _ hx)
  | .succ (p := p) (pre := pre) (res := res) (u := u) (r := r) hp hr hu hrec hx =>
    .succ (p := CoherentShape.reindex τ p) (pre := Tm.presheaf.map τ.op pre) (res := Tm.presheaf.map τ.op res)
      (u := CoherentShape.reindex τ u) (r := CoherentShape.reindex τ r)
      (by
        change X.mem _ (CoherentShape.reindex τ (succMap pre p))
        simpa using X.natural (𝟙 _) τ _ hp) (R.natural hr τ)
      (by
        have h := (rawApplication (B.pullback σ) {pre} (principalIdeal p).val).natural (𝟙 _) τ u hu
        rw [← ΩLower.presheaf_map_mem_id, pullback_rawApplication] at h
        simpa using h)
      (by simpa using NatEvaluates.reindex hrec τ)
      (by
        have h : (application (principalIdeal u) res (principalIdeal r)).mem τ
            (CoherentShape.reindex τ x) := by
          simpa using (application (principalIdeal u) res (principalIdeal r)).natural (𝟙 _) τ x hx
        simpa [pullback_application] using
          (ΩIdeal.presheaf_map_mem_id _ τ _).mpr h)

end

namespace NatEvaluates

variable {D : CodeAssignment} {C : RawAction Γ} {R : NatRecLabelRelation Γ}
  {Z B : RawValue Γ}

theorem map {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {label X y} (h : NatEvaluates D C R Z B σ label X y) {Γ' : Ctx}
    {C' : RawAction Γ'} {R' : NatRecLabelRelation Γ'} {Z' B' : RawValue Γ'} {σ' : Γ₁ ⟶ Γ'}
    (hC : ∀ label I, C.app _ (σ.op, label) I ≤ C'.app _ (σ'.op, label) I)
    (hZ : Z.pullback σ ≤ Z'.pullback σ') (hB : B.pullback σ ≤ B'.pullback σ')
    (hR : ∀ pre res, R.holds σ pre res → R'.holds σ' pre res) :
    NatEvaluates D C' R' Z' B' σ' label X y :=
  have ⟨c, x, hc, hx, hy⟩ := h
  ⟨c, x, hC _ _ _ _ hc, match hx with
    | .bottom hx => .bottom hx
    | .zero hz hx => .zero hz (by simpa using hZ (𝟙 _) _ (by simpa using hx))
    | .succ hp hr hu hrec hx => .succ hp (hR _ _ hr)
        (rawApplication_mono hB Set.Subset.rfl (fun _ _ h => h) _ _ hu)
        (map hrec hC hZ hB hR) hx, hy⟩

theorem eventually {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {label X y}
    (h : NatEvaluates D C R Z B σ label X y)
    {α : Type*} {l : Filter α} {Cs : α → RawAction Γ} {Zs Bs : α → RawValue Γ}
    (hC : ∀ label I {y}, (C.app _ (σ.op, label) I).mem (𝟙 Γ₁) y →
      ∀ᶠ a in l, ((Cs a).app _ (σ.op, label) I).mem (𝟙 Γ₁) y)
    (hZ : ∀ {y}, Z.mem σ y → ∀ᶠ a in l, (Zs a).mem σ y)
    (hB : ∀ {y}, B.mem σ y → ∀ᶠ a in l, (Bs a).mem σ y) :
    ∀ᶠ a in l, NatEvaluates D (Cs a) R (Zs a) (Bs a) σ label X y :=
  have ⟨c, x, hc, hx, hy⟩ := h
  ((hC _ _ hc).and (show ∀ᶠ a in l, NatCaseEvaluates D (Cs a) R (Zs a) (Bs a) σ X x from
    match hx with
    | .bottom hx => Filter.Eventually.of_forall fun _ => .bottom hx
    | .zero hz hx => (hZ hx).mono fun _ hx => .zero hz hx
    | .succ (p := p) hp hr hu hrec hx =>
      ((rawApplication_eventually (Fs := fun a => (Bs a).pullback σ)
        (Xs := fun _ : α => (principalIdeal p).val) (l := l)
        (fun {_} hb => by simpa using hB (by simpa using hb))
        (fun {_} hp => Filter.Eventually.of_forall fun _ => hp) hu).and
        (eventually hrec hC hZ hB)).mono fun _ ⟨hu, hrec⟩ => .succ hp hr hu hrec hx)).mono
    fun _ ⟨hc, hx⟩ => ⟨c, x, hc, hx, hy⟩

end NatEvaluates

noncomputable def natRec (D : CodeAssignment) (C : RawAction Γ) (R : NatRecLabelRelation Γ)
    (Z B : RawValue Γ) : RawAction Γ where
  val.app _ := fun ⟨σ⟩ => ↾fun (label, X) => {
      mem τ y := NatEvaluates D C R Z B (τ ≫ σ) (Tm.presheaf.map τ.op label) (X.pullback τ) y
      natural τ τ' _ h := by simpa using h.reindex τ'
      bottom _ := .bottom
      lower _ hle h := h.lower hle }
  val.naturality τ := fun ⟨σ⟩ => by
    apply ConcreteCategory.hom_ext
    rintro ⟨label, X⟩
    apply ΩLower.ext
    intro Γ₃ υ y
    change NatEvaluates D C R Z B (υ ≫ (τ.unop ≫ σ))
      (Tm.presheaf.map υ.op (Tm.presheaf.map τ label)) ((X.pullback τ.unop).pullback υ) y ↔
        NatEvaluates D C R Z B ((υ ≫ τ.unop) ≫ σ)
          (Tm.presheaf.map (υ ≫ τ.unop).op label) (X.pullback (υ ≫ τ.unop)) y
    simp
  property _ _ _ _ _ h := fun τ _ hy => hy.mono (ΩLower.pullback_mono h τ)

private theorem mem_step (D : CodeAssignment) (C F : RawAction Γ) (R : NatRecLabelRelation Γ)
    (Z B : RawValue Γ) (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (X : RawValue Γ₁)
    (y : CoherentShape Γ₁) :
    ((decode D C (natCase R Z B F)).app _ (σ.op, label) X).mem (𝟙 Γ₁) y ↔
      ∃ c, (C.app _ (σ.op, label) X).mem (𝟙 Γ₁) c ∧ ∃ x,
        (rawNatCase (R.pullback σ) (Z.pullback σ) (B.pullback σ) (F.pullback σ) X).mem (𝟙 Γ₁) x ∧
          (D.eval c (principalIdeal x)).mem (𝟙 Γ₁) y :=
  CodeAssignment.mem_rawExtend ..

private theorem NatCaseEvaluates.iff_mem {σ : Γ₁ ⟶ Γ} {X x} :
    NatCaseEvaluates D C R Z B σ X x ↔
      (rawNatCase (R.pullback σ) (Z.pullback σ) (B.pullback σ)
        ((natRec D C R Z B).pullback σ) X).mem (𝟙 Γ₁) x :=
  ⟨fun
    | .bottom hx => .inl hx
    | .zero hz hx => .inr (.inl ⟨hz, by simpa using hx⟩)
    | .succ hp hr hu hrec hx => .inr (.inr ⟨_, _, _, hp, by simpa using hr, by
        simp [rawNatStep]
        rw [RawAction.pullback, RawAction.app_map, Category.comp_id]
        exact (mem_rawApplication ..).mpr
          (.inr ⟨_, rfl, _, _, hu, by
            change NatEvaluates D C R Z B _ _ _ _
            simpa using hrec, by simpa using hx⟩)⟩),
    fun hx => match (mem_rawNatCase ..).mp hx with
    | .inl hx => .bottom hx
    | .inr (.inl ⟨hz, hx⟩) => .zero hz (by simpa using hx)
    | .inr (.inr ⟨p, pre, res, hp, hr, hx⟩) => by
      simp [rawNatStep] at hx
      rw [RawAction.pullback, RawAction.app_map, Category.comp_id] at hx
      rcases (mem_rawApplication ..).mp hx with hx | ⟨res', hres, u, r, hu, hrec, happ⟩
      · exact .bottom hx
      · obtain rfl := Set.mem_singleton_iff.mp hres
        exact .succ hp (by simpa using hr) hu (by
          change NatEvaluates D C R Z B _ _ _ _ at hrec
          simpa using hrec) (by simpa using happ)⟩

theorem natRec_unfold (D : CodeAssignment) (C : RawAction Γ)
    (R : NatRecLabelRelation Γ) (Z B : RawValue Γ) :
    natRec D C R Z B = decode D C (natCase R Z B (natRec D C R Z B)) := by
  ext Γ₁ ⟨⟨σ⟩, label⟩ X : 1
  apply ΩLower.ext
  intro Γ₂ τ y
  change NatEvaluates D C R Z B (τ ≫ σ) (Tm.presheaf.map τ.op label) (X.pullback τ) y ↔ _
  rw [← ΩLower.presheaf_map_mem_id, ← app_pullback]
  exact ⟨fun ⟨c, x, hc, hx, hy⟩ => (mem_step ..).mpr ⟨c, hc, x, NatCaseEvaluates.iff_mem.mp hx, hy⟩,
    fun h => have ⟨c, hc, x, hx, hy⟩ := (mem_step ..).mp h
      ⟨c, x, hc, NatCaseEvaluates.iff_mem.mpr hx, hy⟩⟩

private theorem NatEvaluates.bound {D : CodeAssignment} {C : RawAction Γ}
    (hC : C.IsIdealValued) {R : NatRecLabelRelation Γ} {Z B : RawValue Γ}
    (hZ : Z.IsDirected) (hB : B.IsDirected) {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {label X y}
    (h : NatEvaluates D C R Z B σ label X y)
    (F : RawAction Γ) (hFI : F.IsIdealValued) (hF : F ≤ natRec D C R Z B)
    (hs : F ≤ decode D C (natCase R Z B F)) :
    ∃ G : RawAction Γ, G.IsIdealValued ∧ G ≤ natRec D C R Z B ∧
      G ≤ decode D C (natCase R Z B G) ∧ F ≤ G ∧ (G.app _ (σ.op, label) X).mem (𝟙 Γ₁) y :=
  have ⟨c, x, hc, hx, hy⟩ := h
  have ⟨G, hGI, hG, ht, hFG, hx⟩ : ∃ G : RawAction Γ, G.IsIdealValued ∧ G ≤ natRec D C R Z B ∧
      G ≤ decode D C (natCase R Z B G) ∧ F ≤ G ∧
        (rawNatCase (R.pullback σ) (Z.pullback σ) (B.pullback σ) (G.pullback σ) X).mem (𝟙 Γ₁) x :=
    match hx with
    | .bottom hx => ⟨F, hFI, hF, hs, le_rfl, (mem_rawNatCase ..).mpr (.inl hx)⟩
    | .zero hz hx => ⟨F, hFI, hF, hs, le_rfl, (mem_rawNatCase ..).mpr (.inr (.inl ⟨hz, by simpa using hx⟩))⟩
    | .succ hp hr hu hrec hx =>
      have ⟨G, hGI, hG, ht, hFG, hrec⟩ := bound hC hZ hB hrec F hFI hF hs
      ⟨G, hGI, hG, ht, hFG, (mem_rawNatCase ..).mpr (.inr (.inr ⟨_, _, _, hp, by simpa using hr, by
        simp [rawNatStep]
        rw [RawAction.pullback, RawAction.app_map, Category.comp_id]
        exact (mem_rawApplication ..).mpr (.inr ⟨_, rfl, _, _, hu, hrec, by simpa using hx⟩)⟩))⟩
  ⟨decode D C (natCase R Z B G), hC.decode D (hGI.natCase R hZ hB), by
    rw [natRec_unfold]
    exact decode_mono D le_rfl (natCase_mono R (fun _ _ h => h) (fun _ _ h => h) hG),
    decode_mono D le_rfl (natCase_mono R (fun _ _ h => h) (fun _ _ h => h) ht), hFG.trans ht,
    (mem_step ..).mpr ⟨c, hc, x, hx, hy⟩⟩

theorem IsIdealValued.natRec (D : CodeAssignment) {C : RawAction Γ}
    (hC : C.IsIdealValued) (R : NatRecLabelRelation Γ) {Z B : RawValue Γ}
    (hZ : Z.IsDirected) (hB : B.IsDirected) : (natRec D C R Z B).IsIdealValued := by
  intro Γ₁ σ label I Γ₂ τ y z hy hz
  have ⟨F, hFI, hF, hs, _, hy⟩ := hy.bound hC hZ hB ⊥
    (fun _ _ _ => ΩLower.isDirected_bot) bot_le bot_le
  have ⟨G, hGI, hG, _, hFG, hz⟩ := hz.bound hC hZ hB F hFI hF hs
  have ⟨w, hw, hyw, hzw⟩ := hGI (τ ≫ σ) (Tm.presheaf.map τ.op label) (I.pullback τ) (𝟙 Γ₂)
    (hFG _ _ _ _ _ hy) hz
  refine ⟨w, ?_, hyw, hzw⟩
  rw [← ΩLower.presheaf_map_mem_id, ← app_pullback]
  exact hG _ _ _ _ _ hw

theorem natRec_mono_parameters (D : CodeAssignment) (R : NatRecLabelRelation Γ)
    {C : RawAction Γ} {Z B : RawValue Γ}
    (hC : C ≤ C') (hZ : Z ≤ Z') (hB : B ≤ B') :
    natRec D C R Z B ≤ natRec D C' R Z' B' :=
  fun _ _ _ _ _ _ h => NatEvaluates.map h (fun _ => hC _ _)
    (ΩLower.pullback_mono hZ _) (ΩLower.pullback_mono hB _) (fun _ _ h => h)

private theorem NatEvaluates.pullback_iff {D : CodeAssignment} {C : RawAction Γ}
    {R : NatRecLabelRelation Γ} {Z B : RawValue Γ} (σ : Γ₁ ⟶ Γ) (τ : Γ₂ ⟶ Γ₁) {label X y} :
    NatEvaluates D (C.pullback σ) (R.pullback σ) (Z.pullback σ) (B.pullback σ) τ label X y ↔
      NatEvaluates D C R Z B (τ ≫ σ) label X y := by
  constructor
  · intro h
    exact h.map (fun _ _ => by rfl)
      (by simp) (by simp) (fun _ _ h => h)
  · intro h
    exact h.map (fun _ _ => by rfl)
      (by simp) (by simp) (fun _ _ h => h)

@[simp] theorem pullback_natRec (D : CodeAssignment) (C : RawAction Γ)
    (R : NatRecLabelRelation Γ) (Z B : RawValue Γ) (σ : Γ₁ ⟶ Γ) :
    (natRec D C R Z B).pullback σ =
      natRec D (C.pullback σ) (R.pullback σ) (Z.pullback σ) (B.pullback σ) := by
  ext Γ₂ ⟨⟨τ⟩, label⟩ X : 1
  rw [RawAction.pullback, RawAction.app_map]
  apply ΩLower.ext
  intro Γ₃ υ y
  change NatEvaluates D C R Z B (υ ≫ (τ ≫ σ)) _ _ _ ↔ _
  change _ ↔ NatEvaluates D (C.pullback σ) (R.pullback σ) (Z.pullback σ) (B.pullback σ) (υ ≫ τ) _ _ _
  rw [NatEvaluates.pullback_iff]
  simp

theorem natRec_eventually (D : CodeAssignment) {α : Type*} {l : Filter α}
    {C : RawAction Γ} {R : NatRecLabelRelation Γ} {Z B : RawValue Γ}
    {Cs : α → RawAction Γ} {Zs Bs : α → RawValue Γ}
    (hC : ∀ label I {y}, (C.app _ ((𝟙 Γ).op, label) I).mem (𝟙 Γ) y →
      ∀ᶠ a in l, ((Cs a).app _ ((𝟙 Γ).op, label) I).mem (𝟙 Γ) y)
    (hZ : ∀ {y}, Z.mem (𝟙 Γ) y → ∀ᶠ a in l, (Zs a).mem (𝟙 Γ) y)
    (hB : ∀ {y}, B.mem (𝟙 Γ) y → ∀ᶠ a in l, (Bs a).mem (𝟙 Γ) y)
    (label : Σ A : Ty Γ, Tm Γ A) (I : RawValue Γ) {y : CoherentShape Γ}
    (hy : ((natRec D C R Z B).app _ ((𝟙 Γ).op, label) I).mem (𝟙 Γ) y) :
    ∀ᶠ a in l, ((natRec D (Cs a) R (Zs a) (Bs a)).app _ ((𝟙 Γ).op, label) I).mem
      (𝟙 Γ) y := by
  change NatEvaluates D C R Z B (𝟙 Γ ≫ 𝟙 Γ)
    (Tm.presheaf.map (𝟙 (Opposite.op Γ)) label) (I.pullback (𝟙 Γ)) y at hy
  change ∀ᶠ a in l, NatEvaluates D (Cs a) R (Zs a) (Bs a) (𝟙 Γ ≫ 𝟙 Γ)
    (Tm.presheaf.map (𝟙 (Opposite.op Γ)) label) (I.pullback (𝟙 Γ)) y
  simp at hy ⊢
  exact hy.eventually hC hZ hB

private theorem NatEvaluates.congr_on_ideals {D : CodeAssignment} {C : RawAction Γ}
    {R : NatRecLabelRelation Γ} {Z B : RawValue Γ} {Γ₁ : Ctx} {σ : Γ₁ ⟶ Γ} {label X y}
    (h : NatEvaluates D C R Z B σ label X y) (hX : X.IsDirected)
    (hC : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : Domain Γ₁),
      C.app _ (σ.op, label) I.val = C'.app _ (σ.op, label) I.val) :
    NatEvaluates D C' R Z B σ label X y :=
  have ⟨c, x, hc, hx, hy⟩ := h
  ⟨c, x, by rwa [← hC _ _ ⟨_, hX⟩], match hx with
    | .bottom hx => .bottom hx
    | .zero hz hx => .zero hz hx
    | .succ hp hr hu hrec hx => .succ hp hr hu (congr_on_ideals hrec (principalIdeal _).property hC) hx, hy⟩

theorem natRec_eq_on_ideals (D : CodeAssignment) {R : NatRecLabelRelation Γ}
    {C : RawAction Γ}
    (hC : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁), C.app _ (σ.op, label) I.val = C'.app _ (σ.op, label) I.val)
    (Z B : RawValue Γ) (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A)
    (I : Domain Γ₁) :
    (natRec D C R Z B).app _ (σ.op, label) I.val =
      (natRec D C' R Z B).app _ (σ.op, label) I.val := by
  apply ΩLower.ext
  intro Γ₂ τ y
  exact ⟨fun h => h.congr_on_ideals (I.pullback τ).property hC,
    fun h => h.congr_on_ideals (I.pullback τ).property (fun σ label I => (hC σ label I).symm)⟩

theorem IsFinitary.natRec (D : CodeAssignment) {C : RawAction Γ}
    (hC : C.IsFinitary) (R : NatRecLabelRelation Γ) (Z B : RawValue Γ) :
    (natRec D C R Z B).IsFinitary := by
  rw [natRec_unfold]
  exact hC.decode D (natCase_isFinitary R Z B _)

theorem natRec_fixed (D : CodeAssignment) (hD : D.IsIdempotent)
    (C : RawAction Γ) (hC : C.IsIdealValued) (R : NatRecLabelRelation Γ)
    (Z B : RawValue Γ) (hZ : Z.IsDirected) (hB : B.IsDirected)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (I : Domain Γ₁) :
    D.rawExtend (C.app _ (σ.op, label) I.val)
      ((natRec D C R Z B).app _ (σ.op, label) I.val) =
      (natRec D C R Z B).app _ (σ.op, label) I.val := by
  have hcase : (natCase R Z B (natRec D C R Z B)).IsIdealValued :=
    IsIdealValued.natCase R hZ hB (IsIdealValued.natRec D hC R hZ hB)
  conv_lhs => rw [natRec_unfold D C R Z B]
  change D.rawExtend _ (D.rawExtend (C.app _ (σ.op, label) I.val)
    ((natCase R Z B (natRec D C R Z B)).app _ (σ.op, label) I.val)) = _
  rw [D.rawExtend_idempotent hD (hC σ label I) (hcase σ label I)]
  exact congrArg (fun F : RawAction Γ => F.app _ (σ.op, label) I.val)
    (natRec_unfold D C R Z B).symm

theorem natRec_zero (D : CodeAssignment) (C : RawAction Γ)
    (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) :
    (natRec D C R Z B).app _ (σ.op, label) (ΩLower.principal pointedOrder zeroAtom) =
      D.rawExtend (C.app _ (σ.op, label) (ΩLower.principal pointedOrder zeroAtom)) (Z.pullback σ) := by
  conv_lhs => rw [natRec_unfold D C R Z B]
  change D.rawExtend (C.app _ (σ.op, label) _) (rawNatCase _ _ _ _ _) = _
  rw [rawNatCase_zero]

theorem natRec_succ (D : CodeAssignment) (C : RawAction Γ)
    (hC : C.IsFinitary) (hCI : C.IsIdealValued) (R : NatRecLabelRelation Γ)
    (Z B : Domain Γ) (σ : Γ₁ ⟶ Γ)
    (label predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A)
    (hrelation : R.holds σ predecessor result) (X : Domain Γ₁) :
    (natRec D C R Z.val B.val).app _ (σ.op, label) (succIdeal predecessor X).val =
      D.rawExtend (C.app _ (σ.op, label) (succIdeal predecessor X).val)
        (rawNatStep B.val (natRec D C R Z.val B.val) σ predecessor result X.val) := by
  have hrel : (R.pullback σ).holds (𝟙 Γ₁) predecessor result := by
    change R.holds (𝟙 Γ₁ ≫ σ) predecessor result
    simpa using hrelation
  have hF : IsFinitary ((natRec D C R Z.val B.val).pullback σ) :=
    IsFinitary.pullback (IsFinitary.natRec D hC R Z.val B.val) σ
  have hFI : IsIdealValued ((natRec D C R Z.val B.val).pullback σ) :=
    IsIdealValued.pullback
    (IsIdealValued.natRec D hCI R Z.property B.property) σ
  conv_lhs => rw [natRec_unfold D C R Z.val B.val]
  change D.rawExtend _ (rawNatCase (R.pullback σ) (Z.val.pullback σ)
    (B.pullback σ).val ((natRec D C R Z.val B.val).pullback σ) _) = _
  rw [rawNatCase_succ hrel (Z.val.pullback σ) (B.pullback σ) _ hF hFI X]
  simp [-pullback_natRec, rawNatStep]
  change D.rawExtend _ (rawApplication _ _
    ((natRec D C R Z.val B.val).app _ (σ.op ≫ 𝟙 _, predecessor) X.val)) = _
  simp
  rfl

end RawAction
end DomainSemantics.CoherentShape
