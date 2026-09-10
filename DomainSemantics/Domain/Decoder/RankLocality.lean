/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Decoder.PiDecoder
public import DomainSemantics.Basis.Rank

@[expose] public section

namespace DomainSemantics.CoherentShape

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}

theorem OutputAtom.principal_upper {f : CoherentGraph Γ} {label : Σ A : Ty Γ, Tm Γ A}
    {x y : CoherentShape Γ} (hy : OutputAtom (principalIdeal f.lamGenerator).val label x y) :
    y ≤ ⊥ ∨ ∃ b : CoherentShape Γ, b.1.rank ≤ f.1.rank ∧
      OutputAtom (principalIdeal f.lamGenerator).val label x b ∧ y ≤ b := by
  obtain ⟨g, i, hg, hlabel, hinput, rfl⟩ := hy
  have hgf : g.lamGenerator ≤ f.lamGenerator := by simpa using hg
  rcases CoherentGraph.lamGenerator_le_iff.mp hgf i with hb | ⟨j, hname, hin, hout⟩
  · exact Or.inl (le_bot_iff.mpr hb)
  · exact Or.inr ⟨f.output j, f.1.rank_outs_le j,
      ⟨f, j, by simp, hname.trans hlabel, hin.trans hinput, rfl⟩, hout⟩

theorem Evaluates.principal_upper {f : CoherentGraph Γ} {label : Σ A : Ty Γ, Tm Γ A}
    {x y : CoherentShape Γ} (hy : Evaluates (principalIdeal f.lamGenerator) label x y) :
    ∃ b : CoherentShape Γ, b.val.rank ≤ f.val.rank ∧
      Evaluates (principalIdeal f.lamGenerator) label x b ∧ y ≤ b := by
  induction hy with
  | entry h =>
    rcases h.principal_upper with hbot | ⟨b, hrb, hb, hyb⟩
    · exact ⟨⊥, Nat.zero_le _, .bottom, hbot⟩
    · exact ⟨b, hrb, .entry hb, hyb⟩
  | bottom => exact ⟨⊥, Nat.zero_le _, .bottom, le_rfl⟩
  | lower h _ ih =>
    have ⟨b, hrb, hb, hyb⟩ := ih
    exact ⟨b, hrb, hb, h.trans hyb⟩
  | join h _ _ ih ih' =>
    have ⟨a, hra, ha, hya⟩ := ih
    have ⟨b, hrb, hb, hyb⟩ := ih'
    have hab := ha.compatible hb
    have ⟨haSup, hbSup⟩ := le_sup hab
    exact ⟨sup a b hab, Shape.rank_cSup.trans (max_le hra hrb), .join hab ha hb,
      sup_le h (hya.trans haSup) (hyb.trans hbSup)⟩

private theorem application_rank_upper_id (f : CoherentGraph Γ) (label : Σ A : Ty Γ, Tm Γ A)
    (X : Domain Γ) {y : CoherentShape Γ}
    (hy : (application (principalIdeal f.lamGenerator) label X).mem (𝟙 Γ) y) :
    ∃ b : CoherentShape Γ, b.val.rank ≤ f.val.rank ∧
      (application (principalIdeal f.lamGenerator) label X).mem (𝟙 Γ) b ∧ y ≤ b := by
  have ⟨x, hx, hy⟩ := (mem_application _ _ _ _ _).mp hy
  simp at hy
  have ⟨b, hrb, hb, hyb⟩ := hy.principal_upper
  exact ⟨b, hrb, (mem_application _ _ _ _ _).mpr ⟨x, hx, by simpa using hb⟩, hyb⟩

theorem application_rank_upper (f : CoherentGraph Γ) (label : Σ A : Ty Γ, Tm Γ A) (X : Domain Γ)
    (σ : Γ₁ ⟶ Γ) {y : CoherentShape Γ₁}
    (hy : (application (principalIdeal f.lamGenerator) label X).mem σ y) :
    ∃ b : CoherentShape Γ₁, b.1.rank ≤ f.1.rank ∧
      (application (principalIdeal f.lamGenerator) label X).mem σ b ∧ y ≤ b := by
  have heq := pullback_application (principalIdeal f.lamGenerator) X label σ
  simp at heq
  change _ = application (principalIdeal (f.reindex σ).lamGenerator) _ _ at heq
  have hy' := (ΩIdeal.presheaf_map_mem_id
    (application (principalIdeal f.lamGenerator) label X) σ y).mpr hy
  rw [heq] at hy'
  have ⟨b, hrb, hb, hyb⟩ := application_rank_upper_id (f.reindex σ) _ _ hy'
  rw [← heq] at hb
  rw [CoherentGraph.reindex_val, Graph.rank_map] at hrb
  exact ⟨b, hrb, (ΩIdeal.presheaf_map_mem_id _ σ _).mp hb, hyb⟩

theorem CodeAssignment.extend_eq_of {F G : CodeAssignment} {P : ∀ {Γ₁ : Ctx}, CoherentShape Γ₁ → Prop}
    (h : ∀ {Γ₁ : Ctx} (b : CoherentShape Γ₁), P b → F.app _ b = G.app _ b) (T X : Domain Γ)
    (hT : ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (a : CoherentShape Γ₁), T.mem σ a →
      ∃ b : CoherentShape Γ₁, P b ∧ T.mem σ b ∧ a ≤ b) :
    F.extend T X = G.extend T X := by
  ext Γ₁ σ y
  simp_rw [mem_extend]
  constructor
  · intro ⟨a, ha, hy⟩
    have ⟨b, hPb, hb, hab⟩ := hT σ a ha
    refine ⟨b, hb, ?_⟩
    simpa [eval, h b hPb] using F.eval_mono_code hab (X.pullback σ) (𝟙 Γ₁) y hy
  · intro ⟨a, ha, hy⟩
    have ⟨b, hPb, hb, hab⟩ := hT σ a ha
    refine ⟨b, hb, ?_⟩
    simpa [eval, h b hPb] using G.eval_mono_code hab (X.pullback σ) (𝟙 Γ₁) y hy

theorem CodeAssignment.piGeneratorOperator_eq_of_rank {F G : CodeAssignment} {n : Nat}
    (h : ∀ {Γ₁ : Ctx} (b : CoherentShape Γ₁), b.1.rank < n → F.app _ b = G.app _ b)
    (a : CoherentShape Γ) (ha : a.1.rank < n) (f : CoherentGraph Γ) (hf : f.1.rank < n) :
    F.piGeneratorOperator a f = G.piGeneratorOperator a f := by
  unfold piGeneratorOperator piOperator
  rw [decode_principal, decode_principal, h a ha]
  congr 1
  ext ⟨Γ₂⟩ ⟨⟨σ⟩, label⟩ ⟨X, Y⟩
  change F.extend ((graphAction f).val.app (Opposite.op Γ₂) (σ.op, label) X) Y =
    G.extend ((graphAction f).val.app (Opposite.op Γ₂) (σ.op, label) X) Y
  rw [graphAction_value]
  refine extend_eq_of h _ _ fun σ₁ _ hz => ?_
  have ⟨b, hrb, hb, hzb⟩ := application_rank_upper _ _ _ σ₁ hz
  rw [CoherentGraph.reindex_val, Graph.rank_map] at hrb
  exact ⟨b, hrb.trans_lt hf, hb, hzb⟩

end DomainSemantics.CoherentShape
