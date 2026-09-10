/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Action

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

def BasisAction.pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : ΩLower pointedOrder Γ)
    (B : BasisAction Γ) : ΩLower pointedOrder Γ where
  mem σ q := ∃ (a : CoherentShape _) (f : CoherentGraph _),
    A.mem σ a ∧ B.GraphValid σ f ∧ q ≤ piGenerator (Ty.pairPresheaf.map σ.op label) a f
  natural σ σ₁ q := fun ⟨a, f, ha, hf, hqf⟩ =>
    ⟨reindex σ₁ a, f.reindex σ₁, A.natural σ σ₁ a ha, hf.reindex σ₁, by
      simp
      exact LE.reindex σ₁ hqf⟩
  bottom σ := ⟨⊥, CoherentGraph.nil _, A.bottom σ, fun i => i.elim0, bot_le⟩
  lower _ hqr := fun ⟨a, f, ha, hf, hrf⟩ => ⟨a, f, ha, hf, hqr.trans hrf⟩

@[simp] theorem BasisAction.mem_pi {Γ₁ Γ₂ : Ctx} (label : Σ A : Ty Γ₂, Ty (Γ₂.extend A))
    (A : ΩLower pointedOrder Γ₂) (B : BasisAction Γ₂) (σ₁ : Γ₁ ⟶ Γ₂)
    (q : CoherentShape Γ₁) :
    (BasisAction.pi label A B).mem σ₁ q ↔
      ∃ (a : CoherentShape Γ₁) (f : CoherentGraph Γ₁),
        A.mem σ₁ a ∧ B.GraphValid σ₁ f ∧ q ≤ piGenerator (Ty.pairPresheaf.map σ₁.op label) a f :=
  Iff.rfl

theorem BasisAction.pullback_pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : ΩLower pointedOrder Γ)
    (B : BasisAction Γ) (σ : Γ₁ ⟶ Γ) :
    (BasisAction.pi label A B).pullback σ =
      BasisAction.pi (Ty.pairPresheaf.map σ.op label) (A.pullback σ)
        (BasisAction.presheaf.map σ.op B) := by
  ext Γ₂ σ₁ q
  rw [ΩLower.presheaf_map_mem, BasisAction.mem_pi, BasisAction.mem_pi]
  change _ ↔ ∃ (a : CoherentShape Γ₂) (f : CoherentGraph Γ₂),
    A.mem (σ₁ ≫ σ) a ∧ B.GraphValid (σ₁ ≫ σ) f ∧
      q ≤ piGenerator (Ty.pairPresheaf.map σ₁.op (Ty.pairPresheaf.map σ.op label)) a f
  simp

@[simp]
theorem BasisAction.mem_piAtom_pi_iff (label : Σ A : Ty Γ, Ty (Γ.extend A))
    (A : ΩLower pointedOrder Γ) (B : BasisAction Γ) (σ : Γ₁ ⟶ Γ)
    (label' : Σ A : Ty Γ₁, Ty (Γ₁.extend A)) :
    (BasisAction.pi label A B).mem σ (piAtom label') ↔ label' = Ty.pairPresheaf.map σ.op label := by
  rw [BasisAction.mem_pi]
  constructor
  · intro ⟨a, f, _, _, hle⟩
    exact label_eq_of_piAtom_le_piGenerator hle
  · intro rfl
    exact ⟨⊥, CoherentGraph.nil Γ₁, A.bottom σ, fun i => i.elim0, le_rfl⟩

theorem BasisAction.pi_isDirected (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : ΩLower pointedOrder Γ)
    (B : BasisAction Γ) (hA : A.IsDirected) (hB : B.IsIdealValued) :
    (BasisAction.pi label A B).IsDirected := by
  intro Γ₁ σ q r ⟨a, f, ha, hf, hqf⟩ ⟨b, g, hb, hg, hrg⟩
  have ⟨c, hc, hac, hbc⟩ := hA σ ha hb
  have hfg := hf.internallyCompatible hB hg
  exact ⟨piGenerator (Ty.pairPresheaf.map σ.op label) c (f.append g hfg),
    ⟨c, f.append g hfg, hc, hf.append hg hfg, le_rfl⟩,
    hqf.trans (piGenerator_le_append_left _ f g hfg hac),
    hrg.trans (piGenerator_le_append_right _ f g hfg hbc)⟩

noncomputable def pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : Domain Γ) (B : IdealAction Γ) : Domain Γ :=
  (BasisAction.pi label A.val B.onBasis).toIdeal
    (BasisAction.pi_isDirected label A.val B.onBasis A.property B.onBasis_isIdealValued)

theorem pullback_pi (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : Domain Γ) (B : IdealAction Γ) (σ : Γ₁ ⟶ Γ) :
    (pi label A B).pullback σ =
      pi (Ty.pairPresheaf.map σ.op label) (A.pullback σ) (B.pullback σ) :=
  Subtype.val_injective (BasisAction.pullback_pi label A.val B.onBasis σ)

@[simp]
theorem mem_piAtom_pi_iff (label : Σ A : Ty Γ, Ty (Γ.extend A)) (A : Domain Γ) (B : IdealAction Γ)
    (σ : Γ₁ ⟶ Γ) (label' : Σ A : Ty Γ₁, Ty (Γ₁.extend A)) :
    (pi label A B).mem σ (piAtom label') ↔ label' = Ty.pairPresheaf.map σ.op label :=
  BasisAction.mem_piAtom_pi_iff label A.val B.onBasis σ label'

end DomainSemantics.CoherentShape
