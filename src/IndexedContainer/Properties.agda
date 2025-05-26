open import Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma using (_×_)

module IndexedContainer.Properties {I : Type} where

open import Definitions I
open import IndexedContainer I as IC using (IndexedContainer; _⊲_; ⟦_⟧; _⇒_; _;_)
open import IndexedContainer.MonoidalCategory {I}

-- interpretation is strong monoidal
module StrongMonoidal where
  module _ (X : I → Type) where
    idᶜ-≃ : ∀ i → ⟦ idᶜ ⟧ X i ≃ X i
    idᶜ-≃ i = isoToEquiv idᶜ-iso
      where
      open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
      open Iso
      idᶜ-iso : Iso (⟦ idᶜ ⟧ X i) (X i)
      idᶜ-iso .fun (_ , x) = x refl
      idᶜ-iso .inv x = _ , λ i≡j → subst X i≡j x
      idᶜ-iso .rightInv x = transportRefl x
      idᶜ-iso .leftInv (_ , x) = ΣPathP
        ( refl
        , implicitFunExt λ {j} → funExt λ i≡j
          → J (λ k i≡k → subst X i≡k (x refl) ≡ x i≡k) (substRefl {B = X} (x refl)) i≡j
        )
        where
          open import Cubical.Data.Sigma using (ΣPathP)

  module _ (F G : IndexedContainer) (X : I → Type) where
    ⊗-≃ : ∀ i → (⟦ F ⟧ » ⟦ G ⟧) X i ≃ ⟦ F ⊗ G ⟧ X i
    ⊗-≃ i = isoToEquiv ⊗-iso where
      open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
      open Iso
      ⊗-iso : Iso ((⟦ F ⟧ » ⟦ G ⟧) X i) (⟦ F ⊗ G ⟧ X i)
      ⊗-iso .fun (s , v) = (s , λ p → v p .fst) , λ { (k , p , q) → v p .snd q }
      ⊗-iso .inv ((s , v) , w) = s , λ p → v p , λ q → w (_ , p , q)
      ⊗-iso .rightInv _ = refl
      ⊗-iso .leftInv  _ = refl

open StrongMonoidal public

-- ICs are fibered over their shapes
module Fibration where
  module _ {S S′ : IType}
    {P : ∀ {i} → S i → IType}
    {P′ : ∀ {i} → S′ i → IType}
    (α : S ⊲ P ⇒ S′ ⊲ P′)
    where

    σ : S i→ S′
    σ i s = α i s .fst
    
    π : ∀ {i} (s : S i) {j} → P′ (σ i s) j → P s j
    π s = α _ s .snd

  module _
    {S : IType}
    {P : {i : I} → S i → (j : I) → Type}
    where

    ∫ : I → I → Type
    ∫ i j = Σ[ s ∈ S i ] P s j

  module _
    {S : IType}
    {P P′ : {i : I} → S i → (j : I) → Type}
    (α : (S ⊲ P) ⇒ (S ⊲ P′)) where
    isVertical : Type
    isVertical = ∀ i → α i » fst ≡ idfun _

  module _
    {S S′ : IType}
    (σ : S i→ S′)
    (P′ : ∀ {i} → S′ i → IType)
    where

    _* : 
      ∀ {i} → S i → IType
    _* s = P′ (σ _ s)

    -- Do we have to factor through σ(S)??
    lift* :
      S ⊲ _* ⇒ S′ ⊲ P′
    lift* i s = σ i s , idfun _

  -- module _ {S S′ : IType}
  --   {P : ∀ {i} → S i → IType}
  --   {P′ : ∀ {i} → S′ i → IType}
  --   (α : S ⊲ P ⇒ S′ ⊲ P′)
  --   where
  --
  --   ↓_ : S ⊲ P ⇒ S ⊲ (σ α *) P′
  --   ↓_ i s = s , π α s
  --
  --   ΣP : I → IType
  --   ΣP i j = Σ[ s ∈ S i ] P s j
  --
  --   forget : ∀ i (s : S i) (s′ : S′ i) j → P′ s′ j → P s j
  --   forget i s j p = {! !}
  --
  --   -- factors : ↓_ ; lift* (σ α) P′ ≡ α 
  --   -- factors = {! !}
  --
  -- module _ {S S′ : IType}
  --   {P : ∀ {i} → S i → IType}
  --   {P′ : ∀ {i} → S′ i → IType}
  --   (α β : S ⊲ P ⇒ S′ ⊲ P′)
  --   where
  --
  --   factoring-≡ :
  --     σ α ≡ σ β
  --     → ↓ α ≡ {! !}
  --     → α ≡ β
  --   factoring-≡ = {! !}
  --
