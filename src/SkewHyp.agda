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

I : Type
I = Unit

module _ (X : Type) where
  lunit : X → I ⊗ X
  lunit x = _ , const x

  runit : X ⊗ I → X
  runit (x , _) = x

module _ (X Y Z : Type) where
  assoc : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z
  assoc (x , yz) = (x , yz » fst) , λ p → yz p .snd p

module _ (M : Type) where
  record MonoidStr : Type where
    field
      u : I → M
      m : M ⊗ M → M

  record isMonoidStr (mstr : MonoidStr) : Type where
    open MonoidStr mstr
    field
      u-unit-l : lunit M » u ⊗₁ idfun M » m ≡ idfun M
      u-unit-r : idfun M ⊗₁ u » m ≡ runit M
      m-assoc  : assoc M M M » m ⊗₁ idfun M » m ≡ idfun M ⊗₁ m » m 

module _ (S : Type) (e : S) (_•_ : S → (P → S) → S) where
  open MonoidStr
  mstr : MonoidStr S
  mstr .u = const e
  mstr .m (s , v) = s • v

  open isMonoidStr
  ismstr : isMonoidStr S mstr
  ismstr .u-unit-l = funExt
    λ s → {! !} -- Goal: (e • (λ x → s)) ≡ s
  ismstr .u-unit-r = funExt
    λ { (s , _) → {! !} } -- Goal: (s • (λ x → e)) ≡ s
  ismstr .m-assoc = funExt λ sv →
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
