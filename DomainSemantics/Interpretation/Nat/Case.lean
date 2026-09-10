/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Nat.Relation
public import DomainSemantics.Interpretation.Application
public import DomainSemantics.Interpretation.Action

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Opposite Presheaf

variable {Γ Γ₁ Γ₂ : Ctx}

noncomputable def rawNatStep (B : RawValue Γ) (F : RawAction Γ) (σ : Γ₁ ⟶ Γ)
    (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) (X : RawValue Γ₁) : RawValue Γ₁ :=
  rawApplication (rawApplication (B.pullback σ) {predecessor} X) {result}
    (F.app _ (σ.op, predecessor) X)

theorem pullback_rawNatStep (B : RawValue Γ) (F : RawAction Γ) (σ : Γ₁ ⟶ Γ)
    (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) (X : RawValue Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (rawNatStep B F σ predecessor result X).pullback σ₁ =
      rawNatStep B F (σ₁ ≫ σ) (Tm.presheaf.map σ₁.op predecessor)
        (Tm.presheaf.map σ₁.op result) (X.pullback σ₁) := by
  unfold rawNatStep
  rw [pullback_rawApplication, pullback_rawApplication,
    ← F.app_pullback σ.op σ₁ predecessor X]
  simp

theorem rawNatStep_mono {B B' : RawValue Γ} {F F' : RawAction Γ}
    (hB : B ≤ B') (hF : F ≤ F') (σ : Γ₁ ⟶ Γ)
    (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) {X X' : RawValue Γ₁} (hX : X ≤ X') :
    rawNatStep B F σ predecessor result X ≤ rawNatStep B' F' σ predecessor result X' :=
  rawApplication_mono
    (rawApplication_mono (ΩLower.pullback_mono hB σ) Set.Subset.rfl hX)
    Set.Subset.rfl (fun σ₁ y hy ↦ hF _ (σ.op, predecessor) X' σ₁ y
      ((F.app _ (σ.op, predecessor)).hom.monotone hX σ₁ y hy))

theorem rawNatStep_toLower (B : Domain Γ)
    (F : RawAction Γ) (hF : F.IsIdealValued) (σ : Γ₁ ⟶ Γ)
    (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    rawNatStep B.val F σ predecessor result X.val =
      (application (application (B.pullback σ) predecessor X) result
        ((F.app _ (σ.op, predecessor) X.val).toIdeal (hF σ predecessor X))).val := by
  unfold rawNatStep
  rw [← ΩIdeal.val_presheaf_map, rawApplication_singleton]
  exact rawApplication_singleton (application (B.pullback σ) predecessor X)
    ((F.app _ (σ.op, predecessor) X.val).toIdeal (hF σ predecessor X)) result

theorem rawNatStep_isDirected {B : RawValue Γ} (hB : B.IsDirected)
    (F : RawAction Γ) (hF : F.IsIdealValued) (σ : Γ₁ ⟶ Γ)
    (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁) :
    (rawNatStep B F σ predecessor result X.val).IsDirected := by
  change (rawNatStep (B.toIdeal hB).val F σ predecessor result X.val).IsDirected
  rw [rawNatStep_toLower (B.toIdeal hB) F hF σ predecessor result X]
  exact (application ..).property

def rawNatCase (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) (X : RawValue Γ) : RawValue Γ where
  mem σ y := y ≤ ⊥ ∨ (X.mem σ zeroAtom ∧ Z.mem σ y) ∨
    ∃ (pred : CoherentShape _) (predecessor result : Σ A : Ty _, Tm _ A),
      X.mem σ (succMap predecessor pred) ∧ R.holds σ predecessor result ∧
        (rawNatStep B F σ predecessor result (ΩLower.principal pointedOrder pred)).mem (𝟙 _) y
  natural σ τ y
    | .inl hy => .inl (LE.reindex τ hy)
    | .inr (.inl ⟨hx, hy⟩) => .inr (.inl ⟨X.natural σ τ zeroAtom hx, Z.natural σ τ y hy⟩)
    | .inr (.inr ⟨p, pre, res, hp, hr, hy⟩) =>
      .inr (.inr ⟨reindex τ p, Tm.presheaf.map τ.op pre, Tm.presheaf.map τ.op res,
        X.natural σ τ _ hp, R.natural hr τ, by
          have h : (rawNatStep B F σ pre res (ΩLower.principal pointedOrder p)).mem τ (reindex τ y) := by
            simpa using (rawNatStep B F σ pre res _).natural (𝟙 _) τ y hy
          have h := (ΩLower.presheaf_map_mem_id _ τ _).mpr h
          rw [pullback_rawNatStep, ΩLower.presheaf_map_principal] at h
          simpa using h⟩)
  bottom _ := .inl le_rfl
  lower σ hyz
    | .inl hz => .inl (hyz.trans hz)
    | .inr (.inl ⟨hx, hz⟩) => .inr (.inl ⟨hx, Z.lower σ hyz hz⟩)
    | .inr (.inr ⟨p, pre, res, hp, hr, hz⟩) =>
      .inr (.inr ⟨p, pre, res, hp, hr, (rawNatStep B F σ pre res _).lower (𝟙 _) hyz hz⟩)

@[simp] theorem mem_rawNatCase (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) (X : RawValue Γ) (σ : Γ₁ ⟶ Γ) (y : CoherentShape Γ₁) :
    (rawNatCase R Z B F X).mem σ y ↔ y ≤ ⊥ ∨
      (X.mem σ zeroAtom ∧ Z.mem σ y) ∨
      ∃ (pred : CoherentShape Γ₁) (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A),
        X.mem σ (succMap predecessor pred) ∧ R.holds σ predecessor result ∧
          (rawNatStep B F σ predecessor result (ΩLower.principal pointedOrder pred)).mem (𝟙 Γ₁) y := Iff.rfl

theorem rawNatCase_mono (R : NatRecLabelRelation Γ)
    {Z Z' B B' X X' : RawValue Γ} {F F' : RawAction Γ}
    (hZ : Z ≤ Z') (hB : B ≤ B') (hF : F ≤ F') (hX : X ≤ X') :
    rawNatCase R Z B F X ≤ rawNatCase R Z' B' F' X' := by
  intro Γ₁ σ y hy
  rcases hy with hy | ⟨hx, hy⟩ | ⟨p, pre, res, hp, hr, hy⟩
  · exact .inl hy
  · exact .inr (.inl ⟨hX σ _ hx, hZ σ _ hy⟩)
  · exact .inr (.inr ⟨p, pre, res, hX σ _ hp, hr,
      rawNatStep_mono hB hF σ pre res (fun _ _ h => h) (𝟙 _) _ hy⟩)

theorem pullback_rawNatCase (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) (X : RawValue Γ) (σ : Γ₁ ⟶ Γ) :
    (rawNatCase R Z B F X).pullback σ =
      rawNatCase (R.pullback σ) (Z.pullback σ) (B.pullback σ) (F.pullback σ)
        (X.pullback σ) := by
  apply ΩLower.ext
  intro Γ₂ τ y
  rw [ΩLower.presheaf_map_mem, mem_rawNatCase, mem_rawNatCase]
  refine or_congr_right (or_congr Iff.rfl (exists_congr fun p => exists_congr fun pre =>
    exists_congr fun res => and_congr_right fun _ => and_congr_right fun _ => ?_))
  simp [rawNatStep]
  rfl

theorem rawNatCase_finitary (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) : ΩLower.IsFinitary (rawNatCase R Z B F) := by
  intro X y hy
  simp_rw [mem_rawNatCase] at hy ⊢
  rcases hy with hy | ⟨hx, hy⟩ | ⟨pred, predecessor, result, hx, hr, hy⟩
  · exact ⟨∅, by simp, Or.inl hy⟩
  · refine ⟨{zeroAtom}, ?_, Or.inr (Or.inl ⟨?_, hy⟩)⟩
    · intro x hx'
      obtain rfl := Finset.mem_singleton.mp hx'
      exact hx
    · simp
  · refine ⟨{succMap predecessor pred}, ?_,
      Or.inr (Or.inr ⟨pred, predecessor, result, ?_, hr, hy⟩)⟩
    · intro x hx'
      obtain rfl := Finset.mem_singleton.mp hx'
      exact hx
    · simp

theorem rawNatCase_isDirected (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) (X : Domain Γ)
    (hZ : Z.IsDirected) (hB : B.IsDirected) (hF : F.IsIdealValued) :
    (rawNatCase R Z B F X.val).IsDirected := by
  intro Γ₁ σ y z hy hz
  simp_rw [mem_rawNatCase] at hy hz ⊢
  change CoherentShape Γ₁ at y z
  have hbot (q : CoherentShape Γ₁) : ⊥ ≤ q := bot_le
  rcases hy with hy | ⟨hx, hy⟩ | ⟨pred, predecessor, result, hx, hr, hy⟩
  · exact ⟨z, hz, (le_trans hy (hbot z)),
      le_refl z⟩
  · rcases hz with hz | ⟨hx', hz⟩ | ⟨pred', predecessor', result', hx', hr', hz⟩
    · exact ⟨y, Or.inr (Or.inl ⟨hx, hy⟩), le_refl y,
        (le_trans hz (hbot y))⟩
    · have ⟨w, hw, hyw, hzw⟩ := hZ σ hy hz
      exact ⟨w, Or.inr (Or.inl ⟨hx, hw⟩), hyw, hzw⟩
    · have ⟨w, _, hw, hw'⟩ := X.property σ hx hx'
      exact (not_compatible_zeroAtom_succMap predecessor' pred'
        (Compatible.of_common_upper hw
          hw')).elim
  · rcases hz with hz | ⟨hx', hz⟩ | ⟨pred', predecessor', result', hx', hr', hz⟩
    · exact ⟨y, Or.inr (Or.inr ⟨pred, predecessor, result, hx, hr, hy⟩),
        le_refl y,
        (le_trans hz (hbot y))⟩
    · have ⟨w, _, hw, hw'⟩ := X.property σ hx' hx
      exact (not_compatible_zeroAtom_succMap predecessor pred
        (Compatible.of_common_upper hw
          hw')).elim
    · have ⟨w, hwX, hw, hw'⟩ := X.property σ hx hx'
      obtain ⟨rfl, hpred⟩ := compatible_succMap_iff.mp (Compatible.of_common_upper hw hw')
      let upper := sup pred pred' hpred
      have ⟨hpredUpper, hpredUpper'⟩ := le_sup hpred
      obtain rfl := R.functional hr hr'
      have hupper : X.mem σ (succMap predecessor upper) :=
        X.lower σ (sup_le (compatible_succMap_iff.mpr ⟨rfl, hpred⟩) hw hw') hwX
      have hmono {p : CoherentShape Γ₁} (hp : p ≤ upper) :
          rawNatStep B F σ predecessor result (ΩLower.principal pointedOrder p) ≤
            rawNatStep B F σ predecessor result (ΩLower.principal pointedOrder upper) :=
        rawNatStep_mono (fun _ _ h ↦ h)
          le_rfl σ predecessor result
          (ΩLower.principal_mono hp)
      have ⟨q, hq, hyq, hzq⟩ := rawNatStep_isDirected hB F hF σ predecessor result
        (principalIdeal upper) (𝟙 Γ₁)
        (hmono hpredUpper (𝟙 Γ₁) y hy)
        (hmono hpredUpper' (𝟙 Γ₁) z hz)
      exact ⟨q, Or.inr (Or.inr ⟨upper, predecessor, result, hupper, hr, hq⟩), hyq, hzq⟩

theorem rawNatCase_zero (R : NatRecLabelRelation Γ) (Z B : RawValue Γ)
    (F : RawAction Γ) :
    rawNatCase R Z B F (ΩLower.principal pointedOrder (zeroAtom : CoherentShape Γ)) = Z := by
  ext Γ₁ σ y
  rw [mem_rawNatCase]
  constructor
  · intro
    | .inl hy =>
      exact Z.lower σ hy (Z.bottom σ)
    | .inr (.inl ⟨_, hy⟩) =>
      exact hy
    | .inr (.inr ⟨pred, predecessor, result, hx, hr, hy⟩) =>
      exact (not_compatible_zeroAtom_succMap predecessor pred
        (Compatible.of_common_upper le_rfl hx)).elim
  · exact fun hy => Or.inr (Or.inl ⟨le_rfl, hy⟩)

theorem rawNatStep_finitary (B : Domain Γ) (F : RawAction Γ)
    (hF : F.IsFinitary) (hD : F.IsIdealValued) (σ : Γ₁ ⟶ Γ)
    (predecessor result : Σ A : Ty Γ₁, Tm Γ₁ A) (X : Domain Γ₁)
    {y : CoherentShape Γ₁}
    (hy : (rawNatStep B.val F σ predecessor result X.val).mem (𝟙 Γ₁) y) :
    ∃ p, X.mem (𝟙 Γ₁) p ∧
      (rawNatStep B.val F σ predecessor result
        (ΩLower.principal pointedOrder p)).mem (𝟙 Γ₁) y := by
  rw [rawNatStep_toLower B F hD σ predecessor result X] at hy
  have ⟨recursive, hrecursive, heval⟩ := (CoherentShape.mem_application _ _ _ _ _).mp hy
  simp at heval
  have ⟨p, hp, heval⟩ := heval.application_argument_finitary
  have ⟨q, hq, hrecursive⟩ := hF.exists_principal σ predecessor X hrecursive
  have ⟨upper, hupper, hpu, hqu⟩ := X.property (𝟙 Γ₁) hp hq
  refine ⟨upper, hupper, ?_⟩
  change (rawNatStep B.val F σ predecessor result (principalIdeal upper).val).mem
    (𝟙 Γ₁) y
  rw [rawNatStep_toLower B F hD σ predecessor result (principalIdeal upper)]
  apply (CoherentShape.mem_application _ _ _ _ _).mpr
  refine ⟨recursive, ?_, ?_⟩
  · exact (F.app _ (σ.op, predecessor)).hom.monotone (ΩLower.principal_mono hqu)
      (𝟙 Γ₁) recursive hrecursive
  · simp
    exact heval.mono_ideal (application_mono_right (B.pullback σ) predecessor
      (ΩLower.principal_mono hpu))

theorem rawNatCase_succ {R : NatRecLabelRelation Γ}
    {predecessor result : Σ A : Ty Γ, Tm Γ A}
    (hrelation : R.holds (𝟙 Γ) predecessor result)
    (Z : RawValue Γ) (B : Domain Γ) (F : RawAction Γ)
    (hF : F.IsFinitary) (hD : F.IsIdealValued) (X : Domain Γ) :
    rawNatCase R Z B.val F (succIdeal predecessor X).val =
      rawNatStep B.val F (𝟙 Γ) predecessor result X.val := by
  ext Γ₁ σ y
  rw [mem_rawNatCase]
  change CoherentShape Γ₁ at y
  have hrelation' : R.holds σ (Tm.presheaf.map σ.op predecessor)
      (Tm.presheaf.map σ.op result) := by
    simpa using R.natural hrelation σ
  have hpull :
      (rawNatStep B.val F (𝟙 Γ) predecessor result X.val).mem σ y ↔
        (rawNatStep B.val F σ (Tm.presheaf.map σ.op predecessor)
          (Tm.presheaf.map σ.op result) (X.pullback σ).val).mem (𝟙 Γ₁) y := by
    rw [← ΩLower.presheaf_map_mem_id
      (rawNatStep B.val F (𝟙 Γ) predecessor result X.val) σ y, pullback_rawNatStep, Category.comp_id,
      ← ΩIdeal.val_presheaf_map]
  constructor
  · intro
    | .inl hy =>
      exact (rawNatStep B.val F (𝟙 Γ) predecessor result X.val).lower σ
        hy
        ((rawNatStep B.val F (𝟙 Γ) predecessor result X.val).bottom σ)
    | .inr (.inl ⟨hx, _⟩) =>
      have ⟨p, _, hp⟩ := (RawValue.mem_succ _ _ _ _).mp hx
      exact (not_compatible_zeroAtom_succMap _ _
        (Compatible.of_common_upper hp (le_rfl))).elim
    | .inr (.inr ⟨pred, pre, res, hx, hr, hy⟩) =>
      have ⟨p, hp, hpred⟩ := (RawValue.mem_succ _ _ _ _).mp hx
      have hsucc : succMap pre pred ≤
          succMap (Tm.presheaf.map σ.op predecessor) p := hpred
      obtain ⟨rfl, hpredLe⟩ := succMap_le_succMap_iff.mp hsucc
      obtain rfl := R.functional hr hrelation'
      apply hpull.mpr
      have hinput : ΩLower.principal pointedOrder pred ≤ (X.pullback σ).val :=
        ΩLower.principal_le_iff.mpr
          ((X.pullback σ).lower (𝟙 Γ₁) hpredLe
            ((ΩIdeal.presheaf_map_mem_id X σ p).mpr hp))
      exact rawNatStep_mono (fun _ _ h ↦ h)
        le_rfl σ _ _ hinput (𝟙 Γ₁) y hy
  · intro hy
    have ⟨p, hp, hy⟩ := rawNatStep_finitary B F hF hD σ _ _ (X.pullback σ) (hpull.mp hy)
    refine Or.inr (Or.inr ⟨p, _, _, ?_, hrelation', hy⟩)
    exact (RawValue.mem_succ _ _ _ _).mpr
      ⟨p, (ΩIdeal.presheaf_map_mem_id X σ p).mp hp, le_rfl⟩

end DomainSemantics.CoherentShape
