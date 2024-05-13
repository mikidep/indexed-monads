open import Cubical.Foundations.Prelude hiding (_∙_)
open import Cubical.Core.Primitives using (Level; ℓ-zero; ℓ-suc)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

module IndexedContainers (indices : Type) where

record IndexedContainer  : Type (ℓ-suc ℓ-zero) where
  field
    shapes : indices → Type
    positions : {i : indices} → shapes i → Type
    positionIndex : {i : indices} {s : shapes i} → positions s → indices

open IndexedContainer

record _⇒_ (F G : IndexedContainer) : Type ℓ-zero where
  field
    smap : (i : indices) → F .shapes i → G .shapes i
    pmap : (i : indices) (s : F .shapes i) → G .positions (smap i s) → F .positions s
    pimap : (i : indices) (s : F .shapes i) (p′ : G .positions (smap i s)) → F. positionIndex (pmap i s p′) ≡ G .positionIndex p′

open _⇒_

id⇒ : ∀ {IC} → IC ⇒ IC
id⇒ .smap i x = x
id⇒ .pmap i s x = x
id⇒ .pimap i s  p′ = refl

idᶜ : IndexedContainer
idᶜ .shapes _ = Unit
idᶜ .positions _ = Unit
idᶜ .positionIndex {i} _ = i

module _ (F : IndexedContainer) where
  private
    S = F .shapes
    P = F .positions
    pi = F .positionIndex

  ⟦_⟧₀ : (indices → Type) → (indices → Type)
  ⟦_⟧₀ X i = Σ[ s ∈ S i ] ((p : P s) → X (pi p))
  -- ⟦ X ⟧₀ i = Σ[ s ∈ S i ] → ∀ j → ((p : P s j) → X j)

  ⟦_⟧₁ : {X Y : indices → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ X ⟧₀ i → ⟦ Y ⟧₀ i)
  ⟦ f ⟧₁ i (s , v) .fst = s
  ⟦ f ⟧₁ i (s , v) .snd p = f (pi p) (v p)



module _ (F G : IndexedContainer) where

  private
    S = F .shapes
    P = F .positions
    pi = F .positionIndex
    S′ = G .shapes
    P′ = G .positions
    pi′ = G .positionIndex
  
  _;_ : IndexedContainer
  _;_ .shapes i = Σ[ s′ ∈ S′ i ] ((p : P′ s′) → S (pi′ p))
  _;_ .positions (s′ , v) = Σ[ p′ ∈ P′ s′ ] (P (v p′))
  _;_ .positionIndex (p′ , p) = pi p

_² : IndexedContainer → IndexedContainer
IC ² = IC ; IC

module _ {F G H K}   where
  _;ₕ_ : (α : F ⇒ H) (β : G ⇒ K) → (F ; G) ⇒ (H ; K)
  (α ;ₕ β) .smap i = let
      αsmap = α .smap
      βsmap = β .smap
      αpmap = α .pmap
      βpmap = β .pmap
    in {! !}
  (α ;ₕ β) .pmap = {! !}
  (α ;ₕ β) .pimap = {! !}

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
      --_∙_ : ∀ {i} (s : S i)
      --  → (∀ {j} (p : P s j) → S j)
      --  → S i
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
      e-unit-l : ∀ i (s : S i) → s ≡ (e i) ∙ λ p → {! subst S (pi-e i p) !} s
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
    ICMS→ICMonad .η .pimap = λ i s p′ → pi-e i p′
    ICMS→ICMonad .μ .smap = λ { i (s , v) → s ∙ v }
    ICMS→ICMonad .μ .pmap = λ { i (s , v) p → (v ↖ p) , (v ↗ p) }
    ICMS→ICMonad .μ .pimap = λ { i (s , v) p′ → pi-∙ i s v p′ }
