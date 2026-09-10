/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Coherent
public import DomainSemantics.Presheaf.Ideal

@[expose] public section

namespace DomainSemantics

open CategoryTheory Opposite Presheaf

variable {Γ Γ₁ : Ctx}

namespace Shape

def cSup {Γ : Ctx} : Shape Γ → Shape Γ → Shape Γ
  | .bot, b => b
  | a, .bot => a
  | .lam k names ins outs, .lam k' names' ins' outs' =>
    .abs (Graph.append ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)
  | .lam _ _ _ _, b => b
  | a, .lam _ _ _ _ => a
  | .forallE label a k names ins outs, .forallE _ a' k' names' ins' outs' =>
    .pi label (cSup a a') (Graph.append ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)
  | .succ name a, .succ _ a' => .succ name (cSup a a')
  | .id A a b, .id A' a' b' => .id (cSup A A') (cSup a a') (cSup b b')
  | a, _ => a

theorem cSup_le {Γ : Ctx} {a b d : Shape Γ} (ha : a ≤ d) (hb : b ≤ d) :
    cSup a b ≤ d := by
  fun_induction cSup a b generalizing d
  · exact hb
  · exact ha
  · cases ha with
    | collapse ha =>
      cases hb with
      | collapse hb => exact .collapse (.lam (Graph.IsBottom.append
          (Basis.IsBottom.abs_iff.mp ha) (Basis.IsBottom.abs_iff.mp hb)))
      | lam hb => exact .lam (Graph.LE.append (.of_isBottom (Basis.IsBottom.abs_iff.mp ha)) hb)
    | lam ha =>
      cases hb with
      | collapse hb => exact .lam (Graph.LE.append ha (.of_isBottom (Basis.IsBottom.abs_iff.mp hb)))
      | lam hb => exact .lam (Graph.LE.append ha hb)
  · exact hb
  · exact ha
  · rename_i ih
    cases ha with
    | collapse h => nomatch h
    | forallE ha hf =>
      cases hb with
      | collapse h => nomatch h
      | forallE hb hg => exact .forallE (ih ha hb) (Graph.LE.append hf hg)
  · rename_i ih
    cases ha with
    | collapse h => nomatch h
    | succ ha =>
      cases hb with
      | collapse h => nomatch h
      | succ hb => exact .succ (ih ha hb)
  · rename_i ihA iha ihb
    cases ha with
    | collapse h => nomatch h
    | id hA ha hab =>
      cases hb with
      | collapse h => nomatch h
      | id hA' hb hbb => exact .id (ihA hA hA') (iha ha hb) (ihb hab hbb)
  · exact ha

theorem le_cSup {a b : Shape Γ} (h : Compatible (𝟙 Γ) a b) :
    a ≤ cSup a b ∧ b ≤ cSup a b := by
  fun_induction cSup a b
  · exact ⟨.bot _, .refl _⟩
  · exact ⟨.refl _, .bot _⟩
  · rename_i k names ins outs k' names' ins' outs'
    exact ⟨.abs (Graph.LE.append_left ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩),
      .abs (Graph.LE.append_right ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)⟩
  · rename_i b hbot hlam
    cases b with
    | bot => exact (hbot rfl).elim
    | lam _ _ _ _ => exact (hlam _ _ _ _ rfl).elim
    | _ => exact ⟨.collapse (.lam h), .refl _⟩
  · rename_i a _ _ _ _ hbot hlam
    cases a with
    | bot => exact (hbot rfl).elim
    | lam _ _ _ _ => exact (hlam _ _ _ _ rfl).elim
    | _ => exact ⟨.refl _, .collapse (.lam h)⟩
  · rename_i label _ k names ins outs label' _ k' names' ins' outs' ih
    have ⟨hl, ha, _⟩ := h
    obtain rfl : label = label' := by simpa using hl
    have ⟨ha, hb⟩ := ih ha
    exact ⟨.pi ha (Graph.LE.append_left ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩),
      .pi hb (Graph.LE.append_right ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)⟩
  · rename_i name _ name' _ ih
    have ⟨hn, ha⟩ := h
    obtain rfl : name = name' := by simpa using hn
    have ⟨ha, hb⟩ := ih ha
    exact ⟨.succ ha, .succ hb⟩
  · rename_i ihA iha ihb
    have ⟨hA, ha, hb⟩ := h
    have ⟨hA, hA'⟩ := ihA hA
    have ⟨ha, ha'⟩ := iha ha
    have ⟨hb, hb'⟩ := ihb hb
    exact ⟨.id hA ha hb, .id hA' ha' hb'⟩
  · rename_i a b hbot hbot' _ hlam hlam' hpi hsucc hid
    fun_cases Compatible (𝟙 Γ) a b
    · exact (hbot rfl).elim
    · exact (hbot' rfl).elim
    · cases h
      exact ⟨.refl _, .refl _⟩
    · exact (hpi _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl).elim
    · exact (hlam _ _ _ _ rfl).elim
    · exact (hlam _ _ _ _ rfl).elim
    · exact (hlam' _ _ _ _ rfl).elim
    · exact ⟨.refl _, .refl _⟩
    · exact ⟨.refl _, .refl _⟩
    · exact (hsucc _ _ _ _ rfl rfl).elim
    · exact (hid _ _ _ _ _ _ rfl rfl).elim
    · simp [Compatible, *] at h

theorem cSup_isCoherent {a b : Shape Γ} (h : Compatible (𝟙 Γ) a b)
    (ha : IsCoherent Γ a) (hb : IsCoherent Γ b) : IsCoherent Γ (cSup a b) := by
  fun_induction cSup a b
  · exact hb
  · exact ha
  · cases ha with | lam hd hi ho =>
      cases hb with | lam hd' hi' ho' => exact .abs (.append ⟨hd, hi, ho⟩ ⟨hd', hi', ho'⟩ h)
  · exact hb
  · exact ha
  · rename_i ih
    have ⟨_, hab, hfg⟩ := h
    cases ha with | forallE ha hd hi ho =>
      cases hb with | forallE hb hd' hi' ho' =>
        exact .pi (ih hab ha hb) (.append ⟨hd, hi, ho⟩ ⟨hd', hi', ho'⟩ hfg)
  · rename_i ih
    have ⟨_, h⟩ := h
    cases ha with | succ ha => cases hb with | succ hb => exact .succ (ih h ha hb)
  · rename_i ihA iha ihb
    have ⟨hAA, haa, hbb⟩ := h
    cases ha with | id hA ha hab =>
      cases hb with | id hA' hb hbc => exact .id (ihA hAA hA hA') (iha haa ha hb) (ihb hbb hab hbc)
  · exact ha

theorem map_cSup {Γ Γ₁ : Ctx} (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (piMap : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A))
    (a b : Shape Γ) : (cSup a b).map arg piMap = cSup (a.map arg piMap) (b.map arg piMap) := by
  induction a generalizing b <;> cases b <;>
    simp_all only [cSup, map, pi, abs]
  all_goals congr 1 <;> funext i <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Graph.append]

theorem cSup_compatible {a b d : Shape Γ} (σ : Γ₁ ⟶ Γ)
    (ha : Compatible σ a d) (hb : Compatible σ b d) : Compatible σ (cSup a b) d := by
  fun_induction cSup a b generalizing d
  · exact hb
  · exact ha
  · cases d with
    | lam _ _ _ _ => exact Graph.Compatible.append_left (h := ⟨_, _, _, _⟩) ha hb
    | bot => trivial
    | _ => exact Graph.IsBottom.append ha hb
  · exact hb
  · exact ha
  · rename_i ih
    cases d with
    | forallE _ _ _ _ _ _ =>
      have ⟨hl, ha, hf⟩ := ha
      have ⟨_, hb, hg⟩ := hb
      exact ⟨hl, ih ha hb, Graph.Compatible.append_left (h := ⟨_, _, _, _⟩) hf hg⟩
    | _ => exact ha
  · rename_i ih
    cases d with
    | succ _ _ =>
      have ⟨hl, ha⟩ := ha
      have ⟨_, hb⟩ := hb
      exact ⟨hl, ih ha hb⟩
    | _ => exact ha
  · rename_i ihA iha ihb
    cases d with
    | id _ _ _ =>
      have ⟨hA, ha, hab⟩ := ha
      have ⟨hA', hb, hbb⟩ := hb
      exact ⟨ihA hA hA', iha ha hb, ihb hab hbb⟩
    | _ => exact ha
  · exact ha

end Shape

namespace CoherentShape

def sup (a b : CoherentShape Γ) (h : Compatible a b) : CoherentShape Γ :=
  ⟨Shape.cSup a.val b.val, Shape.cSup_isCoherent h a.property b.property⟩

theorem le_sup {a b : CoherentShape Γ} (h : Compatible a b) : a ≤ sup a b h ∧ b ≤ sup a b h :=
  Shape.le_cSup h

theorem sup_le {a b d : CoherentShape Γ} (h : Compatible a b) (ha : a ≤ d) (hb : b ≤ d) :
    sup a b h ≤ d := Shape.cSup_le ha hb

theorem Compatible.upper {a b : CoherentShape Γ} (h : Compatible a b) :
    ∃ c : CoherentShape Γ, a ≤ c ∧ b ≤ c := ⟨sup a b h, le_sup h⟩

theorem reindex_sup (σ : Γ₁ ⟶ Γ) {a b : CoherentShape Γ} (h : Compatible a b) :
    reindex σ (sup a b h) = sup (reindex σ a) (reindex σ b) (h.reindex σ) :=
  Subtype.ext (Shape.map_cSup _ _ a.val b.val)

instance : CondSemilatticeSup (CoherentShape Γ) where
  cSup a b h := sup a b (Compatible.of_exists_upper h)
  le_cSup_left _ _ h := have ⟨ha, _⟩ := le_sup (Compatible.of_exists_upper h); ha
  le_cSup_right _ _ h := have ⟨_, hb⟩ := le_sup (Compatible.of_exists_upper h); hb
  cSup_le _ := sup_le _

@[implicit_reducible] noncomputable def pointedOrder : Ctxᵒᵖ ⥤ CondSemilatSup where
  obj Γ₁ := CondSemilatSup.of (CoherentShape Γ₁.unop)
  map σ₁ := CondSemilatSup.ofHom {
    toFun := reindex σ₁.unop
    monotone' _ _ h := LE.reindex σ₁.unop h
    map_bot' := rfl
    map_cSup' _ _ _ _ hda hdb := by
      change reindex σ₁.unop (sup _ _ _) ≤ _
      rw [reindex_sup]
      exact sup_le _ hda hdb }
  map_id _ := CondSemilatSup.ext reindex_id
  map_comp σ₁ σ₂ := CondSemilatSup.ext fun a => (reindex_reindex σ₁.unop σ₂.unop a).symm

@[simp] theorem pointedOrder_map {Γ₁ Γ₂ : Ctxᵒᵖ} (σ₁ : Γ₁ ⟶ Γ₂)
    (a : CoherentShape Γ₁.unop) : pointedOrder.map σ₁ a = reindex σ₁.unop a := rfl

noncomputable abbrev order := pointedOrder ⋙ forget₂ CondSemilatSup Preord

@[simp] theorem order_map {Γ₁ Γ₂ : Ctxᵒᵖ} (σ₁ : Γ₁ ⟶ Γ₂) (a : CoherentShape Γ₁.unop) :
    order.map σ₁ a = reindex σ₁.unop a := rfl

abbrev RawValue (Γ : Ctx) := ΩLower pointedOrder Γ

abbrev Domain (Γ : Ctx) := ΩIdeal pointedOrder Γ

noncomputable abbrev principalIdeal {Γ : Ctx} (a : CoherentShape Γ) : Domain Γ :=
  ΩIdeal.principal pointedOrder a

noncomputable def bottomIdeal (Γ : Ctx) : Domain Γ := principalIdeal ⊥

@[simp] theorem bottomIdeal_eq_bot (Γ₁ : Ctx) : bottomIdeal Γ₁ = ⊥ :=
  ΩIdeal.principal_bottom

@[simp]
theorem pullback_bottomIdeal {Γ₁ Γ : Ctx} (σ : Γ₁ ⟶ Γ) :
    (bottomIdeal Γ).pullback σ = bottomIdeal Γ₁ := by
  unfold bottomIdeal principalIdeal
  simp
  exact congrArg (ΩIdeal.principal pointedOrder)
    (map_bot (ConcreteCategory.hom (pointedOrder.map σ.op)))

@[simp]
theorem principalIdeal_mem {Γ Γ₁ : Ctx} (a : CoherentShape Γ) (σ : Γ₁ ⟶ Γ) (b : CoherentShape Γ₁) :
    (principalIdeal a).mem σ b ↔ b ≤ reindex σ a :=
  ΩIdeal.mem_principal (R := pointedOrder) a σ b

theorem principalIdeal_mono {a b : CoherentShape Γ} (h : a ≤ b) :
    principalIdeal a ≤ principalIdeal b :=
  ΩLower.principal_mono h

end CoherentShape

end DomainSemantics
