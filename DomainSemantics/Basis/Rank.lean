/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import DomainSemantics.Basis.Join

@[expose] public section

namespace DomainSemantics

variable {Γ Γ₁ : Ctx}

def Shape.rank : Shape Γ → Nat
  | .forallE _ a _ _ ins outs =>
    max (rank a) (Finset.univ.sup fun i => max (rank (ins i)) (rank (outs i))) + 1
  | .lam _ _ ins outs => (Finset.univ.sup fun i => max (rank (ins i)) (rank (outs i))) + 1
  | .succ _ a => rank a + 1
  | .id A a b => max (rank A) (max (rank a) (rank b)) + 1
  | _ => 0

def Graph.rank (f : Graph Γ) : Nat :=
  Finset.univ.sup fun i => max (Shape.rank (f.ins i)) (Shape.rank (f.outs i))

namespace Shape

@[simp] theorem rank_map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) :
    ∀ a : Shape Γ, (a.map arg pi).rank = a.rank := by
  intro a
  induction a <;> simp! [*]

end Shape

namespace Graph

theorem le_rank (f : Graph Γ) (i : Fin f.size) :
    max (f.ins i).rank (f.outs i).rank ≤ f.rank :=
  Finset.le_sup (f := fun i => max (f.ins i).rank (f.outs i).rank) (Finset.mem_univ i)

theorem rank_outs_le (f : Graph Γ) (i : Fin f.size) : (f.outs i).rank ≤ f.rank :=
  (le_max_right _ _).trans (f.le_rank i)

theorem rank_append_le (f g : Graph Γ) : (f.append g).rank ≤ max f.rank g.rank := by
  refine Finset.sup_le fun i _ => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa using le_max_of_le_left (f.le_rank i)
  · simpa using le_max_of_le_right (g.le_rank i)

@[simp] theorem rank_map (arg : (Σ A : Ty Γ, Tm Γ A) → Σ A : Ty Γ₁, Tm Γ₁ A) (pi : (Σ A : Ty Γ, Ty (Γ.extend A)) → Σ A : Ty Γ₁, Ty (Γ₁.extend A)) (f : Graph Γ) :
    (f.map arg pi).rank = f.rank := by
  simp! [rank, map]

end Graph

theorem Shape.rank_cSup {a b : Shape Γ} : (a.cSup b).rank ≤ max a.rank b.rank := by
  fun_induction cSup a b
  · exact le_max_right _ _
  · exact le_max_left _ _
  · rename_i k names ins outs k' names' ins' outs'
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    exact Graph.rank_append_le ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩
  · exact le_max_right _ _
  · exact le_max_left _ _
  · rename_i k names ins outs _ _ k' names' ins' outs' ih
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    rw [max_max_max_comm]
    exact max_le_max ih (Graph.rank_append_le ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)
  · rename_i ih
    simpa! only [Nat.add_max_add_right, Nat.add_le_add_iff_right] using ih
  · rename_i ihA iha ihb
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    rw [max_max_max_comm]
    exact max_le_max ihA ((max_le_max iha ihb).trans_eq (max_max_max_comm ..))
  · exact le_max_left _ _

end DomainSemantics
