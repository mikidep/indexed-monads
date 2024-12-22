open import Cubical.Foundations.Prelude public

≡[-]-syntax :
  ∀ {ℓa ℓb}
  {A : Type ℓa}
  {x y : A}
  (p : x ≡ y)
  (B : A → Type ℓb)
  (xb : B x)
  (yb : B y)
  → Type ℓb
≡[-]-syntax p B xb yb = PathP (λ i → B (p i)) xb yb

syntax ≡[-]-syntax p B xb yb = xb ≡[ p , B ] yb
infix 4 ≡[-]-syntax

infixr 5 _$_
_$_ : {ℓ ℓ' : _} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
f $ x = f x

module _
  {ℓ ℓ' ℓ'' : Level}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {C : (a : A) → B a → Type ℓ''} where

  infixl 9 _»_
  _»_ : (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) → (a : A) → C a (f a)
  _»_ f g x = g (f x) 
