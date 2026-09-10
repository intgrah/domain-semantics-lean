/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Universe
public import DomainSemantics.Domain.Nat.Projection
public import DomainSemantics.Basis.Rank
public import DomainSemantics.Domain.Decoder.PiDecoder
import DomainSemantics.Domain.Decoder.RankLocality

@[expose] public section

namespace DomainSemantics.CoherentShape

namespace CodeAssignment

variable {Γ Γ₁ : Ctx}

noncomputable def piStepValue (F : CodeAssignment) (a : Shape Γ) (h : Shape.IsCoherent Γ a) :
    IdealOperator Γ :=
  match a with
  | .sort r => universeOperator r
  | .forallE _ a k names ins outs =>
    F.piGeneratorOperator ⟨a, h.forallE_inv.1⟩ ⟨⟨k, names, ins, outs⟩, h.forallE_inv.2⟩
  | .nat => natOperator
  | _ => IdealOperator.bottom

theorem piStepValue_of_isBottom (F : CodeAssignment) {a : Shape Γ} (h : Basis.IsBottom a)
    (ha : Shape.IsCoherent Γ a) : F.piStepValue a ha = IdealOperator.bottom := by
  cases h <;> rfl

theorem piStepValue_mono (F : CodeAssignment) {a b : Shape Γ} (h : a ≤ b)
    (ha : Shape.IsCoherent Γ a) (hb : Shape.IsCoherent Γ b) :
    F.piStepValue a ha ≤ F.piStepValue b hb := by
  cases h with
  | collapse h =>
    rw [piStepValue_of_isBottom F h]
    exact IdealOperator.bottom_le _
  | forallE ha' hf => exact F.piGeneratorOperator_mono_components ha' hf
  | _ => exact le_rfl

theorem piStepValue_reindex (F : CodeAssignment) (a : Shape Γ) (ha : Shape.IsCoherent Γ a)
    (σ : Γ₁ ⟶ Γ) :
    (F.piStepValue a ha).pullback σ =
      F.piStepValue (a.reindexHom σ) (ha.reindex σ) := by
  cases a with
  | forallE _ a k names ins outs =>
    exact F.pullback_piGeneratorOperator ⟨a, ha.forallE_inv.1⟩
      ⟨⟨k, names, ins, outs⟩, ha.forallE_inv.2⟩ σ
  | _ => rfl

noncomputable def piStep (F : CodeAssignment) : CodeAssignment where
  app _ := Preord.ofHom {
    toFun a := F.piStepValue a.1 a.2
    monotone' a b h := F.piStepValue_mono h a.2 b.2 }
  naturality {_ _} σ₁ := Preord.ext fun ⟨a, ha⟩ => (F.piStepValue_reindex a ha σ₁.unop).symm

theorem piStep_isIdempotent {F : CodeAssignment} (hF : F.IsIdempotent) : F.piStep.IsIdempotent := by
  intro Γ ⟨a, ha⟩ Γ₁ σ X
  cases a with
  | sort r => exact universeIdeal_idempotent r X
  | forallE _ _ _ _ _ _ => exact piGeneratorOperator_isIdempotent hF _ _ σ X
  | nat => exact natIdeal_idempotent X
  | _ => rfl

noncomputable def piStage : Nat → CodeAssignment
  | 0 => bottom
  | n + 1 => (piStage n).piStep

theorem piStage_isIdempotent (n : Nat) : (piStage n).IsIdempotent := by
  induction n with
  | zero => exact bottom_isIdempotent
  | succ n ih => exact piStep_isIdempotent ih

theorem piStepValue_eq_of_rank {F G : CodeAssignment} {n : Nat}
    (h : ∀ {Γ₁ : Ctx} (b : CoherentShape Γ₁), b.1.rank < n → F.app _ b = G.app _ b)
    (a : Shape Γ) (ha : Shape.IsCoherent Γ a) (hr : a.rank ≤ n) :
    F.piStepValue a ha = G.piStepValue a ha := by
  cases a with
  | forallE _ a k names ins outs =>
    have hr' := Nat.lt_of_succ_le hr
    exact piGeneratorOperator_eq_of_rank h ⟨a, ha.forallE_inv.1⟩ ((le_max_left _ _).trans_lt hr')
      ⟨⟨k, names, ins, outs⟩, ha.forallE_inv.2⟩ ((le_max_right _ _).trans_lt hr')
  | _ => rfl

theorem piStage_value_stable (n : Nat) {Γ : Ctx} : ∀ (a : CoherentShape Γ) {k l : Nat},
    a.1.rank ≤ n → n < k → n < l → (piStage k).app _ a = (piStage l).app _ a := by
  induction n using Nat.strong_induction_on generalizing Γ with
  | h n ih =>
    rintro ⟨a, hcoh⟩ (_ | k) (_ | l) ha hk hl <;> simp_all only [Nat.not_lt_zero]
    exact piStepValue_eq_of_rank
      (fun ⟨b, hcoh⟩ hb => ih b.rank hb ⟨b, hcoh⟩ le_rfl
        (hb.trans_le (Nat.le_of_lt_succ hk)) (hb.trans_le (Nat.le_of_lt_succ hl))) a hcoh ha

noncomputable def piLimit : CodeAssignment where
  app _ := Preord.ofHom {
    toFun a := (piStage (a.1.rank + 1)).app _ a
    monotone' a b hab := by
      let m := max a.1.rank b.1.rank + 1
      change (piStage (a.1.rank + 1)).app _ a ≤ (piStage (b.1.rank + 1)).app _ b
      rw [piStage_value_stable _ a le_rfl (Nat.lt_succ_self _) (show a.1.rank < m by omega),
        piStage_value_stable _ b le_rfl (Nat.lt_succ_self _) (show b.1.rank < m by omega)]
      exact ((piStage m).app _).hom.monotone hab }
  naturality {Γ₁ Γ₂} σ₁ := Preord.ext fun ⟨a, ha⟩ => by
    change (piStage ((a.reindexHom σ₁.unop).rank + 1)).app Γ₂ (reindex σ₁.unop ⟨a, ha⟩) =
      IdealOperator.presheaf.map σ₁ ((piStage (a.rank + 1)).app Γ₁ ⟨a, ha⟩)
    rw [Shape.rank_map]
    exact (piStage (a.rank + 1)).app_reindex ⟨a, ha⟩ σ₁.unop

@[simp] theorem piLimit_app (a : CoherentShape Γ) :
    piLimit.app _ a = (piStage (a.1.rank + 1)).app _ a := rfl

theorem piLimit_isIdempotent : piLimit.IsIdempotent := by
  intro Γ₁ ⟨a, ha⟩ _
  rw [piLimit_app]
  exact piStage_isIdempotent (a.rank + 1) ⟨a, ha⟩

theorem piLimit_value_bottom : piLimit.app _ (⊥ : CoherentShape Γ) = IdealOperator.bottom := rfl

end CodeAssignment

end DomainSemantics.CoherentShape
