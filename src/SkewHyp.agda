open import Prelude hiding (I)

open import Cubical.Data.Sigma hiding (I)
open import Cubical.Data.Unit

module SkewHyp (P : Type) where

-- right skew-monoidal
_⊗_ : Type → Type → Type
A ⊗ B = A × (P → B)

module _ {A A′ B B′ : Type} where
  infixl 21 _⊗₁_

  _⊗₁_ : (A → A′) → (B → B′) → A ⊗ B → A′ ⊗ B′ 
  (f ⊗₁ g) (a , pb) = f a , pb » g

I⊗ : Type
I⊗ = Unit

module _ (X : Type) where
  lunit-⊗ : X → I⊗ ⊗ X
  lunit-⊗ x = _ , const x

  runit-⊗ : X ⊗ I⊗ → X
  runit-⊗ (x , _) = x

module _ (X Y Z : Type) where
  assoc-⊗ : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z
  assoc-⊗ (x , yz) = (x , yz » fst) , λ p → yz p .snd p

module _ (M : Type) where
  record isMonoid-⊗ (η : I⊗ → M) (μ : M ⊗ M → M) : Type where
    field
      η-unit-l : lunit-⊗ M » η ⊗₁ idfun M » μ ≡ idfun M
      η-unit-r : idfun M ⊗₁ η » μ ≡ runit-⊗ M
      μ-assoc  : assoc-⊗ M M M » μ ⊗₁ idfun M » μ ≡ idfun M ⊗₁ μ » μ 

  record MonoidStr-⊗ : Type where
    field
      η : I⊗ → M
      μ : M ⊗ M → M
      is-monoid : isMonoid-⊗ η μ
    open isMonoid-⊗ is-monoid public

  record isComonoid (ε : M → I⊗) (δ : M → M ⊗ M) : Type where
    field
      ε-counit-l : δ » ε ⊗₁ idfun M ≡ lunit-⊗ M
      ε-counit-r : δ » idfun M ⊗₁ ε » runit-⊗ M ≡ idfun M
      δ-assoc : δ » idfun M ⊗₁ δ » assoc-⊗ M M M ≡ δ » δ ⊗₁ idfun M
          
  record ComonoidStr : Type where
    field
      ε : M → I⊗
      δ : M → M ⊗ M
      is-comonoid : isComonoid ε δ
    open isComonoid is-comonoid public

Monoid : Type _
Monoid = Σ[ M ∈ Type ] MonoidStr-⊗ M 

module _ (Mon : Monoid) (X : Type) where
  open Σ Mon using () renaming (fst to M)
  open MonoidStr-⊗ (Mon .snd)

  record isLeftAction (f : M ⊗ X → X) : Type where
    field
      act-η : lunit-⊗ X » η ⊗₁ idfun X » f ≡ idfun X
      act-μ : assoc-⊗ M M X » μ ⊗₁ idfun X » f ≡ idfun M ⊗₁ f » f

module _ (S : Type) (e : S) (_•_ : S → (P → S) → S) where
  open MonoidStr-⊗
  open isMonoid-⊗
  mstr : MonoidStr-⊗ S
  mstr .η = const e
  mstr .μ (s , v) = s • v
  mstr .is-monoid .η-unit-l = funExt
    λ s → {! !} -- Goal: (e • (λ x → s)) ≡ s
  mstr .is-monoid .η-unit-r = funExt
    λ { (s , _) → {! !} } -- Goal: (s • (λ x → e)) ≡ s
  mstr .is-monoid .μ-assoc = funExt λ sv →
    let
      s = sv .fst 
      s′ = sv .snd » fst
      s″ = sv .snd » snd
      s′Π•s″ : P → S
      s′Π•s″ p = s′ p • s″ p
      smoosh-s″ : P → S
      smoosh-s″ p = s″ p p
    in {! !} -- Goal: ((s • s′) • smoosh-s″) ≡ (s • s′Π•s″)
    -- Why is smoosh different here?
    -- It might be because this is the cartesian part of a
    -- monoid structure, so it does not act on positions.


