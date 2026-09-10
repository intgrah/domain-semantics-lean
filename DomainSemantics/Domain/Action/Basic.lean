/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Domain.Evaluation
import Mathlib.Data.Fintype.Order

@[expose] public section

namespace DomainSemantics

open CategoryTheory Opposite Presheaf

namespace CoherentShape

noncomputable abbrev BasisAction.presheaf := Functor.parameterizedHom order
  (ΩLower.presheaf pointedOrder) Tm.presheaf

abbrev BasisAction (Γ₁ : Ctx) : Type := BasisAction.presheaf.obj (op Γ₁)

namespace BasisAction

variable {Γ Γ₁ Γ₂ : Ctx}

def IsIdealValued (F : BasisAction Γ) : Prop :=
  ∀ {Γ₁ : Ctx} (σ : Γ₁ ⟶ Γ) (label : Σ A : Ty Γ₁, Tm Γ₁ A) (x : CoherentShape Γ₁),
    (F.app _ (σ.op, label) x).IsDirected

def GraphValid (F : BasisAction Γ) (σ : Γ₁ ⟶ Γ) (f : CoherentGraph Γ₁) : Prop :=
  ∀ i, (F.app _ (σ.op, f.1.names i) (f.input i)).mem (𝟙 Γ₁) (f.output i)

namespace GraphValid

theorem exists_mem {ι : Type*} [Preorder ι] {s : Set ι} (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) {H : ι → BasisAction Γ} {σ : Γ₁ ⟶ Γ}
    (hmono : ∀ label x, Monotone (fun i => (H i).app _ (σ.op, label) x)) {f : CoherentGraph Γ₁}
    (h : ∀ i, ∃ j ∈ s, ((H j).app _ (σ.op, f.1.names i) (f.input i)).mem (𝟙 Γ₁) (f.output i)) :
    ∃ j ∈ s, (H j).GraphValid σ f := by
  choose j hj hout using h
  let g (i : Fin f.1.size) : s := ⟨j i, hj i⟩
  let : Nonempty s := hne.to_subtype
  have ⟨⟨k, hks⟩, hk⟩ := (directedOn_iff_directed.mp hdir).finite_le g
  exact ⟨k, hks, fun i => hmono (f.1.names i) _ (hk i) (𝟙 Γ₁) _ (hout i)⟩

theorem mono {F G : BasisAction Γ} (hFG : F ≤ G) {σ : Γ₁ ⟶ Γ} {f : CoherentGraph Γ₁}
    (hf : GraphValid F σ f) : GraphValid G σ f :=
  fun i => hFG _ (σ.op, f.1.names i) _ (𝟙 Γ₁) _ (hf i)

theorem reindex {F : BasisAction Γ} {σ : Γ₁ ⟶ Γ} {f : CoherentGraph Γ₁} (hf : GraphValid F σ f)
    (σ₁ : Γ₂ ⟶ Γ₁) : GraphValid F (σ₁ ≫ σ) (f.reindex σ₁) := by
  intro i
  have hB' : ((F.app _ (σ.op, f.1.names i) (f.input i)).pullback σ₁).mem (𝟙 Γ₂)
      (CoherentShape.reindex σ₁ (f.output i)) := by
    rw [ΩLower.presheaf_map_mem_id]
    simpa using (F.app _ (σ.op, f.1.names i) (f.input i)).natural (𝟙 Γ₁) σ₁ (f.output i) (hf i)
  exact congrArg (fun L : ΩLower pointedOrder Γ₂ =>
    L.mem (𝟙 Γ₂) (CoherentShape.reindex σ₁ (f.output i)))
    (F.naturality_apply σ₁.op (σ.op, f.1.names i) (f.input i)).symm ▸ hB'

theorem append {F : BasisAction Γ} {σ : Γ₁ ⟶ Γ} {f g : CoherentGraph Γ₁} (hf : GraphValid F σ f)
    (hg : GraphValid F σ g) (hfg : Graph.InternallyCompatible f.1 g.1) :
    GraphValid F σ (f.append g hfg) := fun i =>
  Fin.addCases (fun i => by simpa using hf i) (fun i => by simpa using hg i) i

theorem internallyCompatible {F : BasisAction Γ} {σ : Γ₁ ⟶ Γ} {f g : CoherentGraph Γ₁}
    (hF : F.IsIdealValued) (hf : GraphValid F σ f) (hg : GraphValid F σ g) :
    Graph.InternallyCompatible f.1 g.1 := by
  intro i j Γ₂ σ₁ hlabel hinput
  simp at hlabel hinput ⊢
  have hfi := hf.reindex σ₁ i
  have hgj := hg.reindex σ₁ j
  have ⟨c, hac, hbc⟩ := ((compatible_reindex_iff σ₁ (f.input i) (g.input j)).mpr hinput).upper
  have hfi' := (F.app _ ((σ₁ ≫ σ).op, (f.reindex σ₁).1.names i)).hom.monotone hac (𝟙 Γ₂) _ hfi
  have hgj' := (F.app _ ((σ₁ ≫ σ).op, (g.reindex σ₁).1.names j)).hom.monotone hbc (𝟙 Γ₂) _ hgj
  have hlabel' : (f.reindex σ₁).1.names i = (g.reindex σ₁).1.names j := hlabel
  rw [← hlabel'] at hgj'
  have ⟨d, _, hpd, hqd⟩ := hF (σ₁ ≫ σ) _ c (𝟙 Γ₂) hfi' hgj'
  exact (compatible_reindex_iff σ₁ (f.output i) (g.output j)).mp (Compatible.of_common_upper hpd hqd)

end GraphValid

def abstraction (F : BasisAction Γ) : ΩLower pointedOrder Γ where
  mem σ₁ q := ∃ f : CoherentGraph _, GraphValid F σ₁ f ∧ q ≤ f.lamGenerator
  natural _ σ₂ _ := fun ⟨f, hf, hqf⟩ => ⟨f.reindex σ₂, hf.reindex σ₂, LE.reindex σ₂ hqf⟩
  bottom _ := ⟨CoherentGraph.nil _, fun i => i.elim0, bot_le⟩
  lower _ hqr := fun ⟨f, hf, hrf⟩ => ⟨f, hf, hqr.trans hrf⟩

@[simp] theorem mem_abstraction {Γ₁ Γ₂ : Ctx} (F : BasisAction Γ₂)
    (σ₁ : Γ₁ ⟶ Γ₂) (q : CoherentShape Γ₁) :
    F.abstraction.mem σ₁ q ↔ ∃ f : CoherentGraph Γ₁, GraphValid F σ₁ f ∧ q ≤ f.lamGenerator :=
  Iff.rfl

@[simp]
theorem pullback_abstraction (F : BasisAction Γ) (σ : Γ₁ ⟶ Γ) :
    F.abstraction.pullback σ = abstraction (presheaf.map σ.op F) := by
  ext
  simp [GraphValid]
  rfl

theorem abstraction_isDirected {F : BasisAction Γ} (hF : F.IsIdealValued) :
    F.abstraction.IsDirected := by
  intro Γ₁ σ q r ⟨f, hf, hqf⟩ ⟨g, hg, hrg⟩
  have hfg := hf.internallyCompatible hF hg
  exact ⟨(f.append g hfg).lamGenerator, ⟨f.append g hfg, hf.append hg hfg, le_rfl⟩,
    hqf.trans (CoherentGraph.lamGenerator_le_append_left f g hfg),
    hrg.trans (CoherentGraph.lamGenerator_le_append_right f g hfg)⟩

theorem abstraction_mono {F G : BasisAction Γ} (h : F ≤ G) : F.abstraction ≤ G.abstraction :=
  fun _ _ ⟨f, hf, hqf⟩ => ⟨f, hf.mono h, hqf⟩

theorem mem_value_of_outputAtom {F : BasisAction Γ} {σ : Γ₁ ⟶ Γ} {label : Σ A : Ty Γ₁, Tm Γ₁ A}
    {x y : CoherentShape Γ₁} (h : OutputAtom ((abstraction F).pullback σ) label x y) :
    (F.app _ (σ.op, label) x).mem (𝟙 Γ₁) y := by
  obtain ⟨f, i, hf, hlabel, hix, rfl⟩ := h
  have hf' : (abstraction F).mem σ f.lamGenerator :=
    (ΩLower.presheaf_map_mem_id (abstraction F) σ f.lamGenerator).mp hf
  have ⟨g, hg, hfg⟩ := (mem_abstraction F σ f.lamGenerator).mp hf'
  rcases CoherentGraph.lamGenerator_le_iff.mp hfg i with hbot | ⟨j, hname, hin, hout⟩
  · exact (F.app _ (σ.op, label) x).lower (𝟙 Γ₁)
      (le_bot_iff.mpr hbot) ((F.app _ (σ.op, label) x).bottom (𝟙 Γ₁))
  · have hj := hg j
    rw [hname, hlabel] at hj
    exact (F.app _ (σ.op, label) x).lower (𝟙 Γ₁) hout
      ((F.app _ (σ.op, label)).hom.monotone (hin.trans hix) (𝟙 Γ₁) _ hj)

theorem outputAtom_of_mem_value {F : BasisAction Γ} {σ : Γ₁ ⟶ Γ} {label : Σ A : Ty Γ₁, Tm Γ₁ A}
    {x y : CoherentShape Γ₁} (h : (F.app _ (σ.op, label) x).mem (𝟙 Γ₁) y) :
    OutputAtom ((abstraction F).pullback σ) label x y :=
  let f := CoherentGraph.single label x y
  ⟨f, ⟨0, Nat.one_pos⟩, (ΩLower.presheaf_map_mem_id _ _ _).mpr ⟨f, fun _ => h, le_rfl⟩,
    rfl, le_rfl, rfl⟩

end BasisAction

end CoherentShape

end DomainSemantics
