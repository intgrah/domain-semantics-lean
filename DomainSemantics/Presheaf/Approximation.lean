/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Presheaf.IdealMap
public import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Finite

@[expose] public section

universe u v

namespace DomainSemantics.Presheaf.ΩLower

open CategoryTheory MonoidalCategory Opposite Filter

variable {C : Type u} [Category.{v} C]
variable {R : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {X : C}

def approximations (I : ΩLower R X) : Filter (ΩLower R X) where
  sets := {P | ∃ s : Finset (R.obj (op X)), (∀ x ∈ s, I.mem (𝟙 X) x) ∧
    ∀ J, s.sup (principal R) ≤ J → J ∈ P}
  univ_sets := ⟨∅, by simp, fun _ _ => trivial⟩
  sets_of_superset := fun ⟨s, hs, h⟩ hPQ => ⟨s, hs, fun J hJ => hPQ (h J hJ)⟩
  inter_sets := by
    classical
    intro P Q ⟨s, hs, hP⟩ ⟨t, ht, hQ⟩
    refine ⟨s ∪ t, Finset.forall_mem_union.mpr ⟨hs, ht⟩, fun J hJ => ?_⟩
    exact ⟨@hP J ((Finset.sup_mono (α := ΩLower R X) Finset.subset_union_left).trans hJ),
      @hQ J ((Finset.sup_mono (α := ΩLower R X) Finset.subset_union_right).trans hJ)⟩

theorem exists_finset_of_eventually {I : ΩLower R X} {P : ΩLower R X → Prop}
    (h : ∀ᶠ J in I.approximations, P J) :
    ∃ s : Finset (R.obj (op X)), (∀ x ∈ s, I.mem (𝟙 X) x) ∧ P (s.sup (principal R)) :=
  have ⟨s, hs, hP⟩ := h
  ⟨s, hs, hP _ (fun _ _ ha => ha)⟩

theorem eventually_mem {I : ΩLower R X} {x : R.obj (op X)} (hx : I.mem (𝟙 X) x) :
    ∀ᶠ J in I.approximations, J.mem (𝟙 X) x := by
  refine ⟨{x}, by simpa using hx, ?_⟩
  intro J hJ
  rw [Finset.sup_singleton] at hJ
  exact principal_le_iff.mp hJ

theorem eventually_sup_le {α : Type*} {l : Filter α} {f : α → ΩLower R X}
    (s : Finset (R.obj (op X)))
    (h : ∀ x ∈ s, ∀ᶠ a in l, (f a).mem (𝟙 X) x) :
    ∀ᶠ a in l, s.sup (principal R) ≤ f a :=
  (s.eventually_all.mpr h).mono fun _ h =>
    Finset.sup_le (α := ΩLower R X) fun x hx => principal_le_iff.mpr (h x hx)

variable {S T : Cᵒᵖ ⥤ CondSemilatSup.{max u v}}

def IsFinitary (f : ΩLower R X → ΩLower S X) : Prop :=
  ∀ I {y}, (f I).mem (𝟙 X) y →
    ∃ s : Finset (R.obj (op X)), (∀ x ∈ s, I.mem (𝟙 X) x) ∧
      (f (s.sup (principal R))).mem (𝟙 X) y

variable {U : Cᵒᵖ ⥤ CondSemilatSup.{max u v}} {α : Type*} {l : Filter α}

theorem bind₂_eventually
    (F : Functor.HomObj (R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord)
      (presheaf T) (uliftYoneda.{u}.obj X))
    {I : ΩLower R X} {J : ΩLower S X} {Is : α → ΩLower R X} {Js : α → ΩLower S X}
    (hI : ∀ {x}, I.mem (𝟙 X) x → ∀ᶠ a in l, (Is a).mem (𝟙 X) x)
    (hJ : ∀ {y}, J.mem (𝟙 X) y → ∀ᶠ a in l, (Js a).mem (𝟙 X) y)
    {z} (hz : (bind₂ I J F).mem (𝟙 X) z) : ∀ᶠ a in l, (bind₂ (Is a) (Js a) F).mem (𝟙 X) z := by
  have ⟨x, y, hx, hy, hz⟩ := (mem_bind₂ ..).mp hz
  filter_upwards [hI hx, hJ hy] with a hx hy
  exact (mem_bind₂ ..).mpr ⟨x, y, hx, hy, hz⟩

theorem map₃_eventually
    (F : R ⋙ forget₂ CondSemilatSup Preord ⊗ S ⋙ forget₂ CondSemilatSup Preord ⊗
      T ⋙ forget₂ CondSemilatSup Preord ⟶ U ⋙ forget₂ CondSemilatSup Preord)
    {I : ΩLower R X} {J : ΩLower S X} {K : ΩLower T X}
    {Is : α → ΩLower R X} {Js : α → ΩLower S X} {Ks : α → ΩLower T X}
    (hI : ∀ {x}, I.mem (𝟙 X) x → ∀ᶠ a in l, (Is a).mem (𝟙 X) x)
    (hJ : ∀ {y}, J.mem (𝟙 X) y → ∀ᶠ a in l, (Js a).mem (𝟙 X) y)
    (hK : ∀ {z}, K.mem (𝟙 X) z → ∀ᶠ a in l, (Ks a).mem (𝟙 X) z)
    {w} (hw : (map₃ F I J K).mem (𝟙 X) w) :
    ∀ᶠ a in l, (map₃ F (Is a) (Js a) (Ks a)).mem (𝟙 X) w := by
  have ⟨x, y, z, hx, hy, hz, hw⟩ := (mem_map₃ ..).mp hw
  filter_upwards [hI hx, hJ hy, hK hz] with a hx hy hz
  exact (mem_map₃ ..).mpr ⟨x, y, z, hx, hy, hz, hw⟩

theorem iSup_eventually {ι : Sort*} {F : ι → ΩLower R X} {Fs : α → ι → ΩLower R X}
    (hF : ∀ i {y}, (F i).mem (𝟙 X) y → ∀ᶠ a in l, (Fs a i).mem (𝟙 X) y)
    {y} (hy : (⨆ i, F i).mem (𝟙 X) y) : ∀ᶠ a in l, (⨆ i, Fs a i).mem (𝟙 X) y := by
  rcases (mem_iSup ..).mp hy with hy | ⟨i, hy⟩
  · exact Eventually.of_forall fun _ => (mem_iSup ..).mpr (.inl hy)
  · exact (hF i hy).mono fun _ hy => (mem_iSup ..).mpr (.inr ⟨i, hy⟩)

namespace IsFinitary

protected theorem id : IsFinitary (fun I : ΩLower R X => I) :=
  fun _ y hy => ⟨{y}, by simpa using hy, by simp⟩

protected theorem const (J : ΩLower S X) : IsFinitary (fun _ : ΩLower R X => J) :=
  fun _ _ hy => ⟨∅, by simp, hy⟩

theorem of_eventually {f : ΩLower R X → ΩLower S X}
    (h : ∀ I {y}, (f I).mem (𝟙 X) y → ∀ᶠ J in I.approximations, (f J).mem (𝟙 X) y) :
    IsFinitary f := fun I _ hy => exists_finset_of_eventually (h I hy)

theorem eventually {f : ΩLower R X → ΩLower S X} (hf : IsFinitary f) (hm : Monotone f)
    {α : Type*} {l : Filter α} {I : ΩLower R X} {Is : α → ΩLower R X}
    (hI : ∀ {x}, I.mem (𝟙 X) x → ∀ᶠ a in l, (Is a).mem (𝟙 X) x)
    {y} (hy : (f I).mem (𝟙 X) y) : ∀ᶠ a in l, (f (Is a)).mem (𝟙 X) y :=
  have ⟨s, hs, hy⟩ := hf I hy
  (eventually_sup_le s fun x hx => hI (hs x hx)).mono fun _ h => hm h (𝟙 X) y hy

theorem comp {f : ΩLower R X → ΩLower S X} {g : ΩLower S X → ΩLower T X}
    (hg : IsFinitary g) (hf : IsFinitary f) (hgm : Monotone g) (hfm : Monotone f) :
    IsFinitary (g ∘ f) :=
  of_eventually fun _ _ hy => hg.eventually hgm (hf.eventually hfm eventually_mem) hy

theorem apply {f : ΩLower R X → ΩLower S X → ΩLower T X} {g : ΩLower R X → ΩLower S X}
    (hf : ∀ J, IsFinitary (fun I => f I J)) (harg : ∀ I, IsFinitary (f I))
    (hg : IsFinitary g) (hm : Monotone f) (hargm : ∀ I, Monotone (f I)) (hgm : Monotone g) :
    IsFinitary (fun I => f I (g I)) := by
  apply of_eventually
  intro I y hy
  have ⟨s, hs, hy⟩ := harg I (g I) hy
  filter_upwards
    [eventually_sup_le s fun x hx => hg.eventually hgm eventually_mem (hs x hx),
     (hf (s.sup (principal S))).eventually (fun _ _ h => hm h _) eventually_mem hy]
    with J harg hf
  exact hargm J harg (𝟙 X) y hf

theorem exists_principal {f : ΩLower R X → ΩLower S X} (hf : IsFinitary f) (hm : Monotone f)
    {I : ΩLower R X} (hI : I.IsDirected) {y} (hy : (f I).mem (𝟙 X) y) :
    ∃ x, I.mem (𝟙 X) x ∧ (f (principal R x)).mem (𝟙 X) y :=
  have ⟨_, hs, hy⟩ := hf I hy
  have ⟨x, hx, hsx, _⟩ := hI.exists_principal_between
    (Finset.sup_le (α := ΩLower R X) fun a ha => principal_le_iff.mpr (hs a ha))
  ⟨x, hx, hm hsx (𝟙 X) y hy⟩

end IsFinitary

end DomainSemantics.Presheaf.ΩLower
