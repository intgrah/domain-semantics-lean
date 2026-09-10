# Domain semantics

Definitional inversion for a non-normalising type theory with definitional K via internal Scott domains in presheaves over syntax.
It follows from soundness alone!

This builds on [Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès and Weirich (2026)](https://arxiv.org/pdf/2607.13662) including [digama0/domain-semantics-lean](https://github.com/digama0/domain-semantics-lean).

## Main results

[`Inversion.lean`](DomainSemantics/Inversion.lean)

- `IsDefEq.forallE_inv`: `Γ ⊢ Π A B ≡ Π A' B' : T` gives `Γ ⊢ A ≡ A'`, `A :: Γ ⊢ B ≡ B'`, and `A' :: Γ ⊢ B ≡ B'`.
- `IsDefEq.sort_inv`: `Γ ⊢ sort u ≡ sort v : T` gives `u = v`.
- `IsDefEq.type_unique`: `Γ ⊢ M : A` and `Γ ⊢ M : B` give `Γ ⊢ A ≡ B`.
- `IsDefEq.sort_unique`: `Γ ⊢ M : sort u` and `Γ ⊢ M : sort v` give `u = v`.

## Object language

[Terms (Extrinsic.lean)](DomainSemantics/Syntax/Extrinsic.lean)
[Typing (Typing.lean)](DomainSemantics/Syntax/Typing.lean)

Martin-Löf Type Theory with type-in-type, prop, Π with β-η, proof-irrelevant identity type with transport and K.
