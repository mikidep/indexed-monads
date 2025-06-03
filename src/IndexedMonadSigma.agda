open import Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (idfun; curry; uncurry; _∘_)
open import Cubical.Foundations.Equiv

open import Cubical.Reflection.StrictEquiv

import IndexedContainer as ICModule
open import IndexedContainer.Properties

module IndexedMonadSigma (I : Type) (T : ICModule.IndexedContainer I) where

open ICModule I
open import IndexedContainer.MonoidalCategory {I}

open IndexedContainer T

record RawICMonoid : Type where
  field
    η : idᶜ ⇒ T
    μ : (T ²) ⇒ T

record isICMonoid (raw : RawICMonoid) : Type where
  open RawICMonoid raw
  field
    η-unit-l : unitor-l-inv ; (η ⊗₁ id₁ T) ; μ ≡ id₁ T
    η-unit-r : unitor-r-inv ; (id₁ T ⊗₁ η) ; μ ≡ id₁ T
    μ-assoc : (id₁ T ⊗₁ μ) ; μ ≡ (associator {F = T} ; ((μ ⊗₁ id₁ T) ; μ))

ICMonoid : Type
ICMonoid = Σ RawICMonoid isICMonoid

open import Definitions I
open import Cubical.Foundations.Function using (const)

module _ (i : I) where
  record RawICMSη : Type where
    field
      e : S i
      P-e-idx : P e i→ (i ≡_)

  record RawICMSμ (s : S i) (s′ : P s i→ S) : Type where
    field
      • : S i
      ↑ : ∀ j → P • j → I
      ↖ : ∀ j → (p : P • j) → P s (↑ _ p) 
      ➚ : ∀ j → (p : P • j) → P (s′ (↑ j p) (↖ j p)) j 


module _ 
  (rawη : ∀ {i} → RawICMSη i) 
  (rawμ : ∀ {i} s s′ → RawICMSμ i s s′) where

  module _ {i} where
    open RawICMSη (rawη {i}) public

  open RawICMSμ

  μIη : ∀ {i} (s : S i) → _
  μIη s = rawμ s λ _ _ → e 

  μηI : ∀ {i} (s : S i) → _
  μηI s = rawμ e λ _ pej → subst S (P-e-idx _ pej) s

  μμI : ∀ {i} 
    (s : S i) 
    (s′ : P s i→ S) 
    (s″ : ∀ k (p : P s k) → P (s′ _ p) i→ S) 
    → _
  μμI s s′ s″ = 
    let 
      open RawICMSμ (rawμ s s′) using ()
        renaming (
          • to •μ
        ; ➚ to ➚μ
        ; ↖ to ↖μ
        ) 
    in rawμ •μ λ _ p → s″ _ (↖μ _ p) _ (➚μ _ p)

  μIμ : ∀ {i} 
    (s : S i) 
    (s′ : P s i→ S) 
    (s″ : ∀ k (p : P s k) → P (s′ _ p) i→ S) 
    → _
  μIμ s s′ s″ = rawμ s λ j p → rawμ (s′ _ p) (s″ _ p) .•

  record isICMS-unit
    {i : I} (s : S i) : Type where
    open RawICMSμ (μIη s) using () 
      renaming (
        • to •ul
      ; ↑ to ↑ul
      ; ➚ to ➚ul
      ; ↖ to ↖ul
      ) 
    open RawICMSμ (μηI s) using () 
      renaming (
        • to •ur
      ; ↑ to ↑ur
      ; ➚ to ➚ur
      ; ↖ to ↖ur
      ) 

    field
      unit-l : Path
        (Σ[ t ∈ S i ] P t i→ P s) 
        (•ul , λ _ p → subst (P s) (P-e-idx _ (➚ul _ p)) (↖ul _ p)) 
        (s , i-idfun)

      unit-r : Path
        (Σ[ t ∈ S i ] ∀ j → P t j → Σ[ i′ ∈ I ] Σ[ eqI ∈ i ≡ i′ ] P (subst S eqI s) j)
        (•ur , λ j p → _ , P-e-idx _ (↖ur j p) , ➚ur j p)
        (s   , λ j p → i , refl                , substP T (sym $ substRefl {B = S} s) p)
      
  record isICMS-assoc
    {i : I} 
    (s : S i) 
    (s′ : P s i→ S) 
    (s″ : ∀ k (p : P s k) → P (s′ _ p) i→ S) 
    : Type where

    open RawICMSμ (rawμ s s′) using ()
      renaming (
        • to •μ
      ; ↑ to ↑μ
      ; ➚ to ➚μ
      ; ↖ to ↖μ
      ) 

    •μ′ : ∀ j → P s j → _
    •μ′ = λ j p → rawμ (s′ j p) (s″ j p) .•
    ↑μ′ : ∀ j (p : P s j) → _
    ↑μ′ = λ j p → rawμ (s′ j p) (s″ j p) .↑
    ➚μ′ : ∀ j (p : P s j) → _
    ➚μ′ = λ j p → rawμ (s′ j p) (s″ j p) .➚
    ↖μ′ : ∀ j (p : P s j) → _
    ↖μ′ = λ j p → rawμ (s′ j p) (s″ j p) .↖

    open RawICMSμ (μμI s s′ s″) using () 
      renaming (
        • to •al
      ; ↑ to ↑al
      ; ➚ to ➚al
      ; ↖ to ↖al
      ) 

    open RawICMSμ (μIμ s s′ s″) using () 
      renaming (
        • to •ar
      ; ↑ to ↑ar
      ; ➚ to ➚ar
      ; ↖ to ↖ar
      ) 
      
    field
      assoc : Path
        ( Σ[ t ∈ S i ] (∀ j → P t j → Σ[ k ∈ I ] P s k) 
          × (∀ j → P t j → Σ[ k ∈ I ] P s k) 
          × {! !}
        )
        ( •al 
        , (λ j p → ↑μ _ (↖al _ p) , ↖μ _ (↖al _ p))   
        , (λ j p → ↑al j p , {! !})
        , {!  !}
        )
        ( •ar 
        , (λ j p → ↑ar j p        , ↖ar j p) 
        , (λ j p → ↑μ′ _ _ _ (➚ar _ p) , {! !})
        , {! !}
        )
