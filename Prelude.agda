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

open import Cubical.Foundations.Function using (_$_; idfun) public

module _
  {ℓ ℓ' ℓ'' : Level}
  {A : Type ℓ}
  {B : A → Type ℓ'}
  {C : (a : A) → B a → Type ℓ''} where

  infixl 9 _»_
  _»_ : (f : (a : A) → B a) → (g : {a : A} → (b : B a) → C a b) → (a : A) → C a (f a)
  _»_ f g x = g (f x) 
  {-# INLINE _»_ #-}

infixl -1 _€_

_€_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (a : A) → ((a : A) → B a) → B a
a € f = f a
{-# INLINE _€_ #-}

funExtNonDepHet : {ℓ ℓ′ : Level}
  {A : I → Type ℓ} {B : (i : I) → Type ℓ′}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ((x : A i0) → PathP B (f x) (g (transport (λ ι → A ι) x)))
  → PathP (λ i → A i → B i) f g
funExtNonDepHet {A = A} {B} {f} {g} = invEq (heteroHomotopy≃Homotopy {g = g}) » funExtDep
  where
  open import Cubical.Foundations.Equiv using (invEq)
  open import Cubical.Functions.FunExtEquiv using (funExtDep; heteroHomotopy≃Homotopy)

funExtNonDepHet⁻ : {ℓ ℓ′ : Level}
  {A : I → Type ℓ} {B : (i : I) → Type ℓ′}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → PathP (λ i → A i → B i) f g
  → ((x : A i0) → PathP B (f x) (g (transport (λ ι → A ι) x)))
funExtNonDepHet⁻ {A = A} {B} {f} {g} = funExtDep⁻ » fst (heteroHomotopy≃Homotopy {g = g})
  where
  open import Cubical.Functions.FunExtEquiv using (funExtDep⁻; heteroHomotopy≃Homotopy)
