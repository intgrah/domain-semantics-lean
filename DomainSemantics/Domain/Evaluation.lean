/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Join
public import DomainSemantics.Presheaf.Finitary

@[expose] public section

namespace DomainSemantics

open CategoryTheory Presheaf

variable {Γ Γ₁ : Ctx}
variable {x' y' : CoherentShape Γ}

namespace CoherentShape

theorem compatible_outputs_of_compatible_lamGenerators {f g : CoherentGraph Γ}
    (hfg : Compatible f.lamGenerator g.lamGenerator) (i : Fin f.1.size) (j : Fin g.1.size)
    (hlabel : f.1.names i = g.1.names j) (hinput : Compatible (f.input i) (g.input j)) :
    Compatible (f.output i) (g.output j) := by
  have := hfg i j (𝟙 Γ) (by rw [hlabel]) (by rwa [Category.id_comp])
  simpa

inductive OutputAtom (I : ΩLower pointedOrder Γ) (label : Σ A : Ty Γ, Tm Γ A)
    (x y : CoherentShape Γ) : Prop where
  | intro (graph : CoherentGraph Γ) (entry : Fin graph.val.size)
      (graph_mem : I.mem (𝟙 Γ) graph.lamGenerator) (label_eq : graph.val.names entry = label)
      (input_le : graph.input entry ≤ x) (output_eq : y = graph.output entry) :
      OutputAtom I label x y

namespace OutputAtom

theorem mono {I : ΩLower pointedOrder Γ} {label : Σ A : Ty Γ, Tm Γ A}
    {x y : CoherentShape Γ} (h : OutputAtom I label x y) (hxx' : x ≤ x') :
    OutputAtom I label x' y :=
  let ⟨f, i, hf, hlabel, hix, hy⟩ := h
  ⟨f, i, hf, hlabel, hix.trans hxx', hy⟩

theorem mono_function {I J : ΩLower pointedOrder Γ} (hIJ : I ≤ J)
    {label : Σ A : Ty Γ, Tm Γ A} {x y : CoherentShape Γ} (h : OutputAtom I label x y) :
    OutputAtom J label x y :=
  let ⟨f, i, hf, hlabel, hix, hy⟩ := h
  ⟨f, i, hIJ (𝟙 Γ) f.lamGenerator hf, hlabel, hix, hy⟩

theorem reindex (σ₁ : Γ₁ ⟶ Γ) {I : ΩLower pointedOrder Γ} {label : Σ A : Ty Γ, Tm Γ A}
    {x y : CoherentShape Γ} (h : OutputAtom I label x y) :
    OutputAtom (I.pullback σ₁) (Tm.presheaf.map σ₁.op label) (reindex σ₁ x) (reindex σ₁ y) := by
  have ⟨f, i, hf, hlabel, hix, hiy⟩ := h
  refine ⟨f.reindex σ₁, i, ?_, congrArg (Tm.presheaf.map σ₁.op) hlabel,
    LE.reindex σ₁ hix, congrArg (CoherentShape.reindex σ₁) hiy⟩
  change I.mem ((𝟙 Γ₁) ≫ σ₁) (CoherentShape.reindex σ₁ f.lamGenerator)
  simpa using I.natural (𝟙 Γ) σ₁ f.lamGenerator hf

theorem compatible {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y : CoherentShape Γ}
    (hy : OutputAtom I.val label x y) (hy' : OutputAtom I.val label x y') : Compatible y y' := by
  have ⟨f, i, hf, hilabel, hix, hiy⟩ := hy
  have ⟨g, j, hg, hjlabel, hjx, hjy⟩ := hy'
  have ⟨c, _, hfc, hgc⟩ := I.property (𝟙 Γ) hf hg
  rw [hiy, hjy]
  exact compatible_outputs_of_compatible_lamGenerators (Compatible.of_common_upper hfc hgc) i j
    (hilabel.trans hjlabel.symm) (Compatible.of_common_upper hix hjx)

end OutputAtom

inductive Evaluates (I : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) (x : CoherentShape Γ) :
    CoherentShape Γ → Prop where
  | entry {y} : OutputAtom I.val label x y → Evaluates I label x y
  | bottom : Evaluates I label x ⊥
  | lower {y z} : y ≤ z → Evaluates I label x z → Evaluates I label x y
  | join {y z} (h : Compatible y z) :
      Evaluates I label x y → Evaluates I label x z → Evaluates I label x (sup y z h)

namespace Evaluates

private theorem compatible_right {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y d : CoherentShape Γ}
    (hy : Evaluates I label x y)
    (h : ∀ {z}, OutputAtom I.val label x z → Compatible z d) : Compatible y d := by
  induction hy with
  | entry hy => exact h hy
  | bottom => exact Compatible.of_common_upper bot_le le_rfl
  | lower hle _ ih => exact Shape.Compatible.anti_left hle ih
  | join _ _ _ ih ih' => exact Shape.cSup_compatible _ ih ih'

theorem compatible {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y z : CoherentShape Γ}
    (hy : Evaluates I label x y) (hz : Evaluates I label x z) : Compatible y z :=
  hy.compatible_right fun ha => (hz.compatible_right fun hb => (ha.compatible hb).symm).symm

theorem mono {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x x' y : CoherentShape Γ}
    (hxx' : x ≤ x') (hy : Evaluates I label x y) : Evaluates I label x' y := by
  induction hy with
  | entry h => exact .entry (h.mono hxx')
  | bottom => exact .bottom
  | lower h _ ih => exact .lower h ih
  | join h _ _ ih ih' => exact .join h ih ih'

theorem mono_ideal {I J : Domain Γ} (hIJ : I ≤ J) {label : Σ A : Ty Γ, Tm Γ A}
    {x y : CoherentShape Γ} (hy : Evaluates I label x y) : Evaluates J label x y := by
  induction hy with
  | entry h => exact .entry (h.mono_function hIJ)
  | bottom => exact .bottom
  | lower h _ ih => exact .lower h ih
  | join h _ _ ih ih' => exact .join h ih ih'

theorem reindex (σ : Γ₁ ⟶ Γ) {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y : CoherentShape Γ}
    (hy : Evaluates I label x y) :
    Evaluates (I.pullback σ) (Tm.presheaf.map σ.op label) (CoherentShape.reindex σ x)
      (CoherentShape.reindex σ y) := by
  induction hy with
  | entry h => exact .entry (h.reindex σ)
  | bottom => exact .bottom
  | lower h _ ih => exact .lower (LE.reindex σ h) ih
  | join h _ _ ih ih' => rw [reindex_sup]; exact .join (h.reindex σ) ih ih'

theorem directed {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x x' c y y' : CoherentShape Γ}
    (hxc : x ≤ c) (hx'c : x' ≤ c) (hy : Evaluates I label x y) (hy' : Evaluates I label x' y') :
    ∃ z, Evaluates I label c z ∧ y ≤ z ∧ y' ≤ z := by
  have hy := hy.mono hxc
  have hy' := hy'.mono hx'c
  have h := hy.compatible hy'
  exact ⟨sup y y' h, .join h hy hy', le_sup h⟩

theorem mem_of_outputAtom {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y : CoherentShape Γ}
    {L : RawValue Γ} (hy : Evaluates I label x y) (hL : L.IsDirected)
    (h : ∀ {z}, OutputAtom I.val label x z → L.mem (𝟙 Γ) z) : L.mem (𝟙 Γ) y := by
  induction hy with
  | entry hz => exact h hz
  | bottom => exact L.bottom _
  | lower hle _ ih => exact L.lower _ hle ih
  | join hc _ _ ih ih' =>
    have ⟨z, hz, hyz, hy'z⟩ := hL (𝟙 Γ) ih ih'
    exact L.lower _ (sup_le hc hyz hy'z) hz

theorem le_of_outputAtom {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y d : CoherentShape Γ}
    (hy : Evaluates I label x y) (h : ∀ {z}, OutputAtom I.val label x z → z ≤ d) : y ≤ d := by
  simpa using hy.mem_of_outputAtom (principalIdeal d).property (fun hz => by simpa using h hz)

theorem exists_principal {H : Domain Γ → Domain Γ} (hm : Monotone H) (hf : ΩIdeal.IsFinitary H)
    {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A} {x y : CoherentShape Γ}
    (hy : Evaluates (H I) label x y) :
    ∃ a, I.mem (𝟙 Γ) a ∧ Evaluates (H (principalIdeal a)) label x y := by
  induction hy with
  | entry h =>
    have ⟨g, i, hg, hl, hx, hy⟩ := h
    have ⟨a, ha, hg⟩ := hf I hg
    exact ⟨a, ha, .entry ⟨g, i, hg, hl, hx, hy⟩⟩
  | bottom => exact ⟨⊥, I.bottom _, .bottom⟩
  | lower h _ ih =>
    have ⟨a, ha, hy⟩ := ih
    exact ⟨a, ha, .lower h hy⟩
  | join h _ _ ih ih' =>
    have ⟨a, ha, hy⟩ := ih
    have ⟨b, hb, hy'⟩ := ih'
    have ⟨c, hc, hac, hbc⟩ := I.property (𝟙 Γ) ha hb
    exact ⟨c, hc, .join h (hy.mono_ideal (hm (ΩLower.principal_mono hac)))
      (hy'.mono_ideal (hm (ΩLower.principal_mono hbc)))⟩

theorem function_ideal_finitary {I : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A}
    {input output : CoherentShape Γ} (h : Evaluates I label input output) :
    ∃ f, I.mem (𝟙 Γ) f ∧ Evaluates (principalIdeal f) label input output :=
  h.exists_principal monotone_id (fun _ y hy => ⟨y, hy, by simp⟩)

end Evaluates

def application (I : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) (X : Domain Γ) : Domain Γ where
  val := {
    mem σ y := ∃ x, X.mem σ x ∧ Evaluates (I.pullback σ) (Tm.presheaf.map σ.op label) x y
    natural σ σ₁ y := fun ⟨x, hx, hy⟩ =>
      ⟨reindex σ₁ x, X.natural σ σ₁ x hx, by simpa using hy.reindex σ₁⟩
    bottom σ := ⟨⊥, X.bottom σ, Evaluates.bottom⟩
    lower _ hyy' := fun ⟨x, hx, hy'⟩ => ⟨x, hx, hy'.lower hyy'⟩ }
  property {_} σ {_ _} := fun ⟨x, hx, hxy⟩ ⟨x', hx', hx'y'⟩ =>
    have ⟨c, hc, hxc, hx'c⟩ := X.property σ hx hx'
    have ⟨z, hcz, hyz, hy'z⟩ := Evaluates.directed hxc hx'c hxy hx'y'
    ⟨z, ⟨c, hc, hcz⟩, hyz, hy'z⟩

@[simp] theorem mem_application {Γ₁ Γ₂ : Ctx} (I : Domain Γ₂) (label : Σ A : Ty Γ₂, Tm Γ₂ A)
    (X : Domain Γ₂) (σ₁ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    (application I label X).mem σ₁ y ↔ ∃ x, X.mem σ₁ x ∧
      Evaluates (I.pullback σ₁) (Tm.presheaf.map σ₁.op label) x y :=
  Iff.rfl

theorem OutputAtom.mem_application {F X : Domain Γ} {label : Σ A : Ty Γ, Tm Γ A}
    {x y : CoherentShape Γ} (hy : OutputAtom F.val label x y) (hx : X.mem (𝟙 Γ) x) :
    (application F label X).mem (𝟙 Γ) y := by
  simp
  exact ⟨x, hx, .entry hy⟩

theorem application_mono_left {I J : Domain Γ} (hIJ : I ≤ J) (label : Σ A : Ty Γ, Tm Γ A)
    (X : Domain Γ) : application I label X ≤ application J label X :=
  fun σ _ ⟨x, hx, hxy⟩ => ⟨x, hx, hxy.mono_ideal (ΩIdeal.pullback_mono hIJ σ)⟩

theorem application_mono_right (I : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) {X Y : Domain Γ}
    (hXY : X ≤ Y) : application I label X ≤ application I label Y :=
  fun σ _ ⟨x, hx, hxy⟩ => ⟨x, hXY σ x hx, hxy⟩

theorem application_argument_finitary (F : Domain Γ) (label : Σ A : Ty Γ, Tm Γ A) :
    ΩIdeal.IsFinitary (application F label) :=
  fun I y ⟨x, hx, heval⟩ => ⟨x, hx, x, by simp, heval⟩

end CoherentShape

end DomainSemantics
