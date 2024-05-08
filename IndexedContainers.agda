open import Cubical.Foundations.Prelude hiding (_∙_)
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

module IndexedContainers (indices : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    shapes : indices → Type
    positions : {i : indices} → shapes i → Type
    positionIndex : {i : indices} {s : shapes i} → positions s → indices

open IndexedContainer

record _⇒_ (IC₁ IC₂ : IndexedContainer) : Type ℓ-zero where
  field
    smap : (i : indices) → IC₁ .shapes i → IC₂ .shapes i
    pmap : (i : indices) (s : IC₁ .shapes i) → IC₂ .positions (smap i s) → IC₁ .positions s

open _⇒_

id⇒ : ∀ {IC} → IC ⇒ IC
id⇒ .smap i x = x
id⇒ .pmap i s x = x

idᶜ : IndexedContainer
idᶜ .shapes _ = Unit
idᶜ .positions _ = Unit
idᶜ .positionIndex {i} _ = i


module _ (IC₁ IC₂ : IndexedContainer) where

  S = IC₁ .shapes
  P = IC₁ .positions
  pi = IC₁ .positionIndex
  S′ = IC₂ .shapes
  P′ = IC₂ .positions
  pi′ = IC₂ .positionIndex
  
  _·_ : IndexedContainer
  _·_ .shapes i = Σ[ s ∈ S i ] ((p : P s) → S′ (pi p))
  _·_ .positions (s , v) = Σ[ p ∈ P s ] (P′ (v p))
  _·_ .positionIndex (p , p′) = pi′ p′

_² : IndexedContainer → IndexedContainer
IC ² = IC · IC

_;ₕ_ : ∀ {F G S T} → F ⇒ S → G ⇒ T → (F · G) ⇒ (S · T)
_;ₕ_ = {! !}

module _ 
    (S : indices → Type)
    (P : {i : indices} → S i → Type)
    (pi : {i : indices} {s : S i} → P s → indices) where

  T : IndexedContainer
  T .shapes = S
  T .positions = P
  T .positionIndex = pi

  record ICMonad : Type ℓ-zero where
    field
      η : idᶜ ⇒ T
      μ : (T ²) ⇒ T

  open ICMonad

  record ICMS : Type ℓ-zero where
    field
      e  : ∀ i → S i
      _∙_ : ∀ {i} (s : S i)
        → ((p : P s) → S (pi p))
        → S i
      _↖_ : ∀ {i} {s : S i}
        → (v : (p : P s) → S (pi p))
        → P (s ∙ v)
        → P s
      _↗_ : ∀ {i} {s : S i}
        → (v : (p : P s) → S (pi p))
        → (p′ : P (s ∙ v))
        → P (v (v ↖ p′))

      pi-e : ∀ i (p : P (e i)) → i ≡ pi p
      pi-∙ : ∀ i s (v : (p : P s) → S (pi p)) (p : P (s ∙ v)) → pi (v ↗ p) ≡ pi p
      e-unit-l : ∀ i (s : S i) → s ≡ (e i) ∙ λ p → subst S (pi-e i p) s
      e-unit-r : ∀ i (s : S i) → s ≡ s ∙ λ p → e (pi p) 
      ∙-assoc : ∀ i 
        (s : S i)
        (v : (p : P s) → S (pi p))
        (w :  (p : P s) → (p′ : P (v p)) → S (pi p′))
        → ((s ∙ v) ∙ λ p → subst S (pi-∙ i s v p) (w (v ↖ p) (v ↗ p))) ≡ s ∙ (λ p → v p ∙ w p)


  module _ (icms : ICMS) where
    open ICMS icms

    ICMS→ICMonad : ICMonad
    ICMS→ICMonad .η .smap = λ i _ → e i
    ICMS→ICMonad .η .pmap = λ _ _ _ → tt
    ICMS→ICMonad .μ .smap = λ { i (s , v) → s ∙ v }
    ICMS→ICMonad .μ .pmap = λ { i (s , v) p → (v ↖ p) , (v ↗ p) }
